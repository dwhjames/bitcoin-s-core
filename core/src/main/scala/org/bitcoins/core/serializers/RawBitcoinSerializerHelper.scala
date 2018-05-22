package org.bitcoins.core.serializers

import org.bitcoins.core.number.UInt64
import org.bitcoins.core.protocol.{ CompactSizeUInt, NetworkElement }
import org.bitcoins.core.util.BitcoinSLogger

/**
 * Created by chris on 2/18/16.
 */
sealed abstract class RawSerializerHelper {
  private val logger = BitcoinSLogger.logger

  /**
   * Used parse a byte sequence to a Seq[TransactionInput], Seq[TransactionOutput], etc
   * Makes sure that we parse the correct amount of elements
   */
  def parseCmpctSizeUIntSeq[T <: NetworkElement](bytes: scodec.bits.ByteVector, constructor: scodec.bits.ByteVector => T): (Seq[T], scodec.bits.ByteVector) = {
    val count = CompactSizeUInt.parse(bytes)
    val payload = bytes.splitAt(count.size.toInt)._2
    def loop(accum: Seq[T], remaining: scodec.bits.ByteVector): (Seq[T], scodec.bits.ByteVector) = {
      if (accum.size == count.num.toInt) {
        (accum.reverse, remaining)
      } else {
        val parsed = constructor(remaining)
        val (_, newRemaining) = remaining.splitAt(parsed.size)
        loop(parsed +: accum, newRemaining)
      }
    }

    val (parsed, remaining) = loop(Nil, payload)
    require(parsed.size == count.num.toInt, "Could not parse the amount of required elements, got: " + parsed.size + " required: " + count)
    (parsed, remaining)
  }

  /** Writes a Seq[TransactionInput]/Seq[TransactionOutput]/Seq[Transaction] -> scodec.bits.ByteVector */
  def writeCmpctSizeUInt[T](ts: Seq[T], serializer: T => scodec.bits.ByteVector): scodec.bits.ByteVector = {
    val serialized = ts.flatMap(serializer(_))
    val cmpct = CompactSizeUInt(UInt64(ts.size))
    cmpct.bytes ++ serialized
  }
}

object RawSerializerHelper extends RawSerializerHelper
