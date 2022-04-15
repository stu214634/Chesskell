{-# LANGUAGE BinaryLiterals#-}
{-# LANGUAGE TemplateHaskell #-}
module Templates where

import Data.Word (Word64)
import Data.Bits ((.&.), Bits (bit, (.|.), unsafeShiftR, unsafeShiftL), FiniteBits (countTrailingZeros))
import Language.Haskell.TH
import Data.Functor ((<&>))
import BitFuncs


-- These things should go in their own module, and shouldn't be re-exported
-- from this one. I just dragged them in here from somewhere they *can't* be.

-- | Masks out the most significant bit of every byte
firstBitMask :: Word64
firstBitMask = 0x7F7F7F7F7F7F7F7F

-- | Masks out everything except the most significant bit of every byte
firstBits :: Word64
firstBits = 0x8080808080808080

-- | Masks out the least significant bit of every byte
lastBitMask :: Word64
lastBitMask = 0xFEFEFEFEFEFEFEFE

-- | Masks out everything except the least significant bit of every byte
lastBits :: Word64
lastBits = 0x0101010101010101

-- | Masks out the bottom column of bits
bottomRowMask :: Word64
bottomRowMask = 0x00000000000000FF

-- | Masks out the columns in the given Word64
colMasksXXXXXXXX :: Word64 -> Word64
colMasksXXXXXXXX 0 = 0
colMasksXXXXXXXX n =
    let col = countTrailingZeros n
    in (lastBits `unsafeShiftL` col) .|.
         colMasksXXXXXXXX ((n `unsafeShiftR` (col+1)) `unsafeShiftL` (col+1))

mirrorBitsY :: Word64 -> Q Exp
mirrorBitsY w = [| res |]
  where
    res =
      let bytes = w64Tow8L w
      in foldl1 (.|.) [ (bytes !! i) `unsafeShiftL` (i*8) | i <- [0..7]]

kingTableT :: Word64 -> Word64
kingTableT x =
  let n = bit (fromIntegral x)
  in ((n `unsafeShiftL` 1 .|. n `unsafeShiftL` 9 .|. n `unsafeShiftR` 7) .&. colMasksXXXXXXXX 0b11111110)
                 .|. ((n `unsafeShiftR` 1 .|. n `unsafeShiftR` 9 .|. n `unsafeShiftL` 7) .&. colMasksXXXXXXXX 0b01111111)
                 .|. n `unsafeShiftR` 8
                 .|. n `unsafeShiftL` 8

knightTableT :: Word64 -> Word64
knightTableT x =
  let n = bit (fromIntegral x)
    in ((n `unsafeShiftL` 10 .|. n `unsafeShiftR` 6) .&. colMasksXXXXXXXX 0b11111100)
       .|. (( n `unsafeShiftL` 17 .|. n `unsafeShiftR` 15) .&. colMasksXXXXXXXX 0b11111110)
       .|. ((n `unsafeShiftL` 6 .|. n `unsafeShiftR` 10) .&. colMasksXXXXXXXX 0b00111111)
       .|. ((n `unsafeShiftL` 15 .|. n `unsafeShiftR` 17) .&. colMasksXXXXXXXX 0b01111111)

mkTable :: String -> (Word64 -> Word64) -> Q Exp
mkTable nm fun = lamCaseE $
  ([0..63] <&> \n -> let funn = fun n
                     in match (litP (integerL (toInteger n))) (normalB [| funn |] ) [])
  ++ [match wildP (normalB [| error err |]) []]
  where
    err = nm ++ ": invalid index"
