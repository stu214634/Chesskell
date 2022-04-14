{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Model where
import Data.Word (Word64)
import GHC.Generics ( Generic )
import Control.Parallel.Strategies ( NFData )
import Data.Bits ((.&.), unsafeShiftR, Bits (unsafeShiftL))
import Data.Char (chr)
import GHC.Base (ord)
import qualified Data.HashTable.IO as H
import Data.Hashable


-- | Hash Depth Type Flag, Eval, Occurence count 
type TT = H.CuckooHashTable ChessState (Int, Int, Int, Int, Int)

-- | A BitBoard represantation of Chess
data BitBoard = BitBoard {
    whitePawns :: {-# UNPACK #-} !Word64,
    whiteKnights :: {-# UNPACK #-} !Word64,
    whiteBishops :: {-# UNPACK #-} !Word64,
    whiteRooks :: {-# UNPACK #-} !Word64,
    whiteQueens :: {-# UNPACK #-} !Word64,
    whiteKing :: {-# UNPACK #-} !Word64,
    blackPawns :: {-# UNPACK #-} !Word64,
    blackKnights :: {-# UNPACK #-} !Word64,
    blackBishops :: {-# UNPACK #-} !Word64,
    blackRooks :: {-# UNPACK #-} !Word64,
    blackQueens :: {-# UNPACK #-} !Word64,
    blackKing :: {-# UNPACK #-} !Word64
} deriving (Generic, NFData, Eq)


data ChessState = ChessState {
    board :: {-# UNPACK #-} !BitBoard,
    white :: !Bool,
    castling :: {-# UNPACK #-} !Word64,
    enPassant :: {-# UNPACK #-} !Word64,
    halfMoveClock :: {-# UNPACK #-} !Word64,
    fullMoveNumber :: {-# UNPACK #-} !Word64,
    zobristHash :: {-# UNPACK #-} !Word64
} deriving (Generic, NFData, Eq)

instance Hashable ChessState where
    hashWithSalt _ state = fromIntegral $ zobristHash state

{-
    Encoding a Move in a Word64
    00000000 00000000 00000000 01111111 source square
    00000000 00000000 00111111 10000000 destination square
    00000000 00000011 11000000 00000000 piece
    00000000 00111100 00000000 00000000 promotion piece
    00000000 01000000 00000000 00000000 capture
    00000000 10000000 00000000 00000000 en passant
    00000001 00000000 00000000 00000000 castling
    00000010 00000000 00000000 00000000 double pawn push
-}

type Move = Word64

-- | Decodes a castle to a string
decodeCastle :: Word64 -> String
decodeCastle 0 = "-"
decodeCastle x =
    (if x .&. 1 /= 0 then "K" else "") ++
    (if x .&. 2 /= 0 then "Q" else "") ++
    (if x .&. 4 /= 0 then "k" else "") ++
    (if x .&. 8 /= 0 then "q" else "")


instance Show ChessState where
    show (ChessState b t c eP hmc fmc zsh) =
        show b ++
        (if t then "White" else "Black") ++ " to Move\nPossible Castles: " ++
        (if c == 0 then "-" else decodeCastle c) ++ "\n" ++
        "EnPassant target: " ++ if eP == 0 then "-" else showPos eP ++ "\nHalf Moves: " ++
        show hmc ++ "\nFull Moves: " ++
        show fmc ++ "\n" ++
        show zsh ++ "\n"

showBits :: Word64 -> Int -> String
showBits _ 0 = ""
showBits x n = showBits (x `unsafeShiftR` 1) (n-1) ++ show (x .&. 1)
showRow :: Word64 -> String
showRow x = showBits x 8 ++ "\n"
showRows :: Word64 -> Int -> String
showRows _ 0 = "\n"
showRows x n = showRow (fromIntegral (x `unsafeShiftR` 56)) ++ showRows (x `unsafeShiftL` 8) (n-1)
showRows8 :: Word64 -> String
showRows8 x = showRows x 8

showBits32 :: Int -> Word64 -> String
showBits32 0 _ = ""
showBits32 n x = showBits32 (n-1) (x `unsafeShiftR` 1) ++ show (x .&. 1)
instance Show BitBoard where
    show (BitBoard wp wn wb wr wq wk bp bn bb br bq bk) =
            "wp:\n" ++ showRows8 wp ++ "wn:\n" ++ showRows8 wn ++ "wb:\n" ++ showRows8 wb ++ "wr:\n" ++ showRows8 wr ++ "wq:\n" ++ showRows8 wq ++ "wk:\n" ++ showRows8 wk ++
            "bp:\n" ++ showRows8 bp ++ "bn:\n" ++ showRows8 bn ++ "bb:\n" ++ showRows8 bb ++ "br:\n" ++ showRows8 br ++ "bq:\n" ++ showRows8 bq ++ "bk:\n" ++ showRows8 bk

-- | Maps a Word64 index to a Chess Position String
showPos :: Word64 -> String
showPos x = [chr (ord 'h' - fromIntegral x `mod` 8), chr (ord '1' + fromIntegral x `div` 8)]

-- | Maps a Chess Piece Char to a Word64
parsePiece :: Char -> Word64
parsePiece 'P' = 0
parsePiece 'N' = 1
parsePiece 'B' = 2
parsePiece 'R' = 3
parsePiece 'Q' = 4
parsePiece 'K' = 5
parsePiece 'p' = 6
parsePiece 'n' = 7
parsePiece 'b' = 8
parsePiece 'r' = 9
parsePiece 'q' = 10
parsePiece 'k' = 11
parsePiece _ = error "Invalid piece"

-- | Maps a Word64 to a Chess Piece Char
showPiece :: Word64 -> Char
showPiece 0 = 'P'
showPiece 1 = 'N'
showPiece 2 = 'B'
showPiece 3 = 'R'
showPiece 4 = 'Q'
showPiece 5 = 'K'
showPiece 6 = 'p'
showPiece 7 = 'n'
showPiece 8 = 'b'
showPiece 9 = 'r'
showPiece 10 = 'q'
showPiece 11 = 'k'
showPiece _ = '?'


-- | Getters for moves 
getSource :: Move -> Word64
getSource m = m .&. 127
getDestination :: Move -> Word64
getDestination m = unsafeShiftR m 7 .&. 127
getPiece :: Move -> Word64
getPiece m = unsafeShiftR m 14 .&. 15
getPromotion :: Move -> Word64
getPromotion m = unsafeShiftR m 18 .&. 15
getCapture :: Move -> Bool
getCapture m = unsafeShiftR m 22 .&. 1 == 1
getEnPassant :: Move -> Bool
getEnPassant m = unsafeShiftR m 23 .&. 1 == 1
getCastle :: Move -> Bool
getCastle m = unsafeShiftR m 24 .&. 1 == 1
getDoublePawnPush :: Move -> Bool
getDoublePawnPush m = unsafeShiftR m 25 .&. 1 == 1
