{-# LANGUAGE BinaryLiterals#-}
{-# LANGUAGE TemplateHaskell #-}
module Templates where

import Data.Word (Word64)
import Data.Bits ((.&.), Bits (bit, (.|.), unsafeShiftR, unsafeShiftL), FiniteBits (countTrailingZeros))
import Language.Haskell.TH ( Exp, Q )

-- | Masks out the columns in the given Word64
colMasksXXXXXXXX :: Word64 -> Q Exp
colMasksXXXXXXXX 0 = [|0|]
colMasksXXXXXXXX n = do
    let col = countTrailingZeros n
    [|(lastBits `unsafeShiftL` col) .|. $(colMasksXXXXXXXX ((n `unsafeShiftR` (col+1)) `unsafeShiftL` (col+1)))|]

mirrorBitsY :: Word64 -> Q Exp
mirrorBitsY w = [|let bytes = w64Tow8L w in
    foldl1 (.|.) [ (bytes !! i) `unsafeShiftL` (i*8) | i <- [0..7]]|]

kingTableT :: Word64 -> Q Exp
kingTableT x = [|let n = bit x in ((n `unsafeShiftL` 1 .|. n `unsafeShiftL` 9 .|. n `unsafeShiftR` 7) .&. $(colMasksXXXXXXXX 0b11111110))
                 .|. ((n `unsafeShiftR` 1 .|. n `unsafeShiftR` 9 .|. n `unsafeShiftL` 7) .&. $(colMasksXXXXXXXX 0b01111111)) .|. n `unsafeShiftR` 8 .|. n `unsafeShiftL` 8|]

knightTableT :: Word64 -> Q Exp
knightTableT x = [|let n = bit x in ((n `unsafeShiftL` 10 .|. n `unsafeShiftR` 6) .&. $(colMasksXXXXXXXX 0b11111100))
                    .|. (( n `unsafeShiftL` 17 .|. n `unsafeShiftR` 15) .&. $(colMasksXXXXXXXX 0b11111110))
                    .|. ((n `unsafeShiftL` 6 .|. n `unsafeShiftR` 10) .&. $(colMasksXXXXXXXX 0b00111111))
                    .|. ((n `unsafeShiftL` 15 .|. n `unsafeShiftR` 17) .&. $(colMasksXXXXXXXX 0b01111111))|]



