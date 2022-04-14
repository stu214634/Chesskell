{-# LANGUAGE BangPatterns #-}
module BitFuncs where

import Data.Word (Word64)
import Model (BitBoard (BitBoard))
import Data.Bits ((.&.), Bits (complement, bit, (.|.), unsafeShiftR), FiniteBits (countTrailingZeros))

word64ToInt :: Word64 -> Int
word64ToInt = fromIntegral
intToWord64 :: Int -> Word64
intToWord64 = fromIntegral

-- | Used to determine what piece is at position idx. 
-- | This terminates after a full loop (at the lates) but returns undefined garbage since the recursion depth is unclear, this fix is not ideal and exists to make enPassant captures not crash.
pieceAt :: BitBoard  -> Int -> Int
pieceAt (BitBoard 0 0 0 0 0 0 0 0 0 0 0 0) _ = 0
pieceAt (BitBoard wp wn wb wr wq wk bp bn bb br bq bk) idx = case wp .&. bit idx of
    0 ->  1 + pieceAt (BitBoard wn wb wr wq wk bp bn bb br bq bk 0) idx
    _ -> 0
    
-- | Clears all bits at the index on the given bitboard
clearBits :: BitBoard -> Word64 -> BitBoard
clearBits (BitBoard wp wn wb wr wq wk bp bn bb br bq bk) i =
    BitBoard (clearBit wp i) (clearBit wn i) (clearBit wb i) (clearBit wr i) (clearBit wq i) (clearBit wk i) (clearBit bp i) (clearBit bn i) (clearBit bb i) (clearBit br i) (clearBit bq i) (clearBit bk i)

-- | Clears the bit at the given index.
clearBit :: Word64 -> Word64 -> Word64
clearBit b i = b .&. complement (bit $ word64ToInt i)

-- | Sets the bit at the given index.
setBit :: Word64 -> Word64 -> Word64
setBit b i = b .|. bit (word64ToInt i)

clearBit8 :: Word64 -> Word64 -> Word64
clearBit8 b i = b .&. complement (bit $ word64ToInt i)

-- | Clears the lsbit and returns its index.
popLSB :: Word64 -> (Word64, Word64)
popLSB b = (trailI, rest)
    where
        !rest = b .&. (b-1)
        !trailI = intToWord64 $ countTrailingZeros b

w64Tow8L :: Word64 -> [Word64]
w64Tow8L w = [ (w `unsafeShiftR` (i*8)) .&. 0xFF | i <- [7,6,5,4,3,2,1,0]]
