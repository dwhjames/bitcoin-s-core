package org.bitcoins.core.serializers.script

import org.bitcoins.core.number.UInt64
import org.bitcoins.core.protocol.CompactSizeUInt
import org.bitcoins.core.protocol.script.ScriptWitness
import org.bitcoins.core.serializers.RawBitcoinSerializer
import org.bitcoins.core.util.BitcoinSUtil

import scala.annotation.tailrec

/**
 * Created by chris on 12/14/16.
 */
sealed abstract class RawScriptWitnessParser extends RawBitcoinSerializer[ScriptWitness] {

  def read(bytes: scodec.bits.ByteVector): ScriptWitness = {
    //first byte is the number of stack items
    val stackSize = CompactSizeUInt.parseCompactSizeUInt(bytes)
    val (_, stackBytes) = bytes.splitAt(stackSize.size.toInt)
    @tailrec
    def loop(remainingBytes: scodec.bits.ByteVector, accum: Seq[scodec.bits.ByteVector], remainingStackItems: UInt64): Seq[scodec.bits.ByteVector] = {
      if (remainingStackItems <= UInt64.zero) accum
      else {
        val elementSize = CompactSizeUInt.parseCompactSizeUInt(remainingBytes)
        val (_, stackElementBytes) = remainingBytes.splitAt(elementSize.size.toInt)
        val stackElement = stackElementBytes.take(elementSize.num.toInt)
        val (_, newRemainingBytes) = stackElementBytes.splitAt(stackElement.size)
        loop(newRemainingBytes, stackElement +: accum, remainingStackItems - UInt64.one)
      }
    }
    //note there is no 'reversing' the accum, in bitcoin-s we assume the top of the stack is the 'head' element in the sequence
    val stack = loop(stackBytes, Nil, stackSize.num)
    val witness = ScriptWitness(stack)
    witness
  }

  def write(scriptWitness: ScriptWitness): scodec.bits.ByteVector = {
    @tailrec
    def loop(remainingStack: Seq[scodec.bits.ByteVector], accum: Seq[scodec.bits.ByteVector]): Seq[scodec.bits.ByteVector] = {
      if (remainingStack.isEmpty) accum.reverse
      else {
        val compactSizeUInt: CompactSizeUInt = CompactSizeUInt.calc(remainingStack.head)
        val serialization: scodec.bits.ByteVector = compactSizeUInt.bytes ++ remainingStack.head
        loop(remainingStack.tail, serialization +: accum)
      }
    }
    val stackItems: Seq[scodec.bits.ByteVector] = loop(scriptWitness.stack.reverse, Nil)
    val size = CompactSizeUInt(UInt64(stackItems.size))
    (size.bytes +: stackItems).flatten
  }
}

object RawScriptWitnessParser extends RawScriptWitnessParser
