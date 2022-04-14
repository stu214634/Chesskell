{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

{-#LANGUAGE BinaryLiterals#-}
module MoveApplication where

import Data.Word (Word64)
import Model (Move, ChessState (ChessState), BitBoard (BitBoard), getSource, getDestination, getPiece, getPromotion, getCapture, getEnPassant, getCastle, getDoublePawnPush)
import Data.Bits ( Bits((.|.), (.&.), bit, xor))
import BitFuncs (clearBit8, clearBit, setBit, clearBits, word64ToInt )
import Zobrist (zBlack, zCastle, zEnPassant, xorPieceAt, xorAt)

-- | Gets the corresponding Word64 for a given piece
getPieceBits :: BitBoard -> Word64 -> Word64
getPieceBits (BitBoard wp _ _ _ _ _ _ _ _ _ _ _) 0 = wp
getPieceBits (BitBoard _ wn _ _ _ _ _ _ _ _ _ _) 1 = wn
getPieceBits (BitBoard _ _ wb _ _ _ _ _ _ _ _ _) 2 = wb
getPieceBits (BitBoard _ _ _ wr _ _ _ _ _ _ _ _) 3 = wr
getPieceBits (BitBoard _ _ _ _ wq _ _ _ _ _ _ _) 4 = wq
getPieceBits (BitBoard _ _ _ _ _ wk _ _ _ _ _ _) 5 = wk
getPieceBits (BitBoard _ _ _ _ _ _ bp _ _ _ _ _) 6 = bp
getPieceBits (BitBoard _ _ _ _ _ _ _ bn _ _ _ _) 7 = bn
getPieceBits (BitBoard _ _ _ _ _ _ _ _ bb _ _ _) 8 = bb
getPieceBits (BitBoard _ _ _ _ _ _ _ _ _ br _ _) 9 = br
getPieceBits (BitBoard _ _ _ _ _ _ _ _ _ _ bq _) 10 = bq
getPieceBits (BitBoard _ _ _ _ _ _ _ _ _ _ _ bk) 11 = bk

-- | Gets all White pieces
getWhitePieces :: BitBoard -> Word64
getWhitePieces (BitBoard wp wn wb wr wq wk _ _ _ _ _ _) = wp .|. wn .|. wb .|. wr .|. wq .|. wk

-- | Gets all Black pieces
getBlackPieces :: BitBoard -> Word64
getBlackPieces (BitBoard _ _ _ _ _ _ bp bn bb br bq bk) = bp .|. bn .|. bb .|. br .|. bq .|. bk

-- | Get all pieces
getAllPieces :: BitBoard -> Word64
getAllPieces (BitBoard wp wn wb wr wq wk bp bn bb br bq bk) = wp .|. wn .|. wb .|. wr .|. wq .|. wk .|. bp .|. bn .|. bb .|. br .|. bq .|. bk

-- | filteredCastlingRights bases on the destination
filteredCastlingRights ::(Word64, Word64) -> Word64 ->(Word64, Word64)
filteredCastlingRights (zHash, castlingRights) destination = case destination of
    0 -> if castlingRights .&. 0b00000001 /= 0 then (zHash `xor` zCastle 0, clearBit8 castlingRights 0) else (zHash, castlingRights)
    7 -> if castlingRights .&. 0b00000010 /= 0 then (zHash `xor` zCastle 1, clearBit8 castlingRights 1) else (zHash, castlingRights)
    56 -> if castlingRights .&. 0b00000100 /= 0 then (zHash `xor` zCastle 2, clearBit8 castlingRights 2) else (zHash, castlingRights)
    63 -> if castlingRights .&. 0b00001000 /= 0 then (zHash `xor` zCastle 3, clearBit8 castlingRights 3) else (zHash, castlingRights)
    _ -> (zHash, castlingRights)

-- | Applies a move to a ChessState.
applyMove :: ChessState -> Move -> ChessState
-- | White Moves
applyMove (ChessState (BitBoard wp wn wb wr wq wk bp bn bb br bq bk) True castlingRights enPassantTarget halfMoveClock fullMoveclock zHash) move =
    let
        source = getSource move
        destination = getDestination move
        piece = getPiece move
        promotion = getPromotion move
        capture = getCapture move
        enPassant = getEnPassant move
        castle = getCastle move
        doublePush = getDoublePawnPush move
    in
        applyMove' source destination piece promotion capture enPassant castle doublePush
    where
        state = ChessState (BitBoard wp wn wb wr wq wk bp bn bb br bq bk) True castlingRights enPassantTarget halfMoveClock fullMoveclock zHash
        applyMove' :: Word64 -> Word64 -> Word64 -> Word64 -> Bool -> Bool -> Bool -> Bool -> ChessState
        -- | Pawn Moves
        -- | Normal Pawn Move
        applyMove' source destination 0 0 False False _ False =
            let
                newPawns = clearBit wp source
                newPawns' = setBit newPawns destination
                nHash = xorPieceAt (xorPieceAt zHash 0 source) 0 destination `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
            in
                ChessState (BitBoard newPawns' wn wb wr wq wk bp bn bb br bq bk) False castlingRights 0 0 fullMoveclock nHash
        -- | Normal Pawn Capture
        applyMove' source destination 0 0 True False _ False =
            let
                newPawns = clearBit wp source
                (BitBoard np' wn' wb' wr' wq' wk' bp' bn' bb' br' bq' bk') = clearBits (BitBoard newPawns wn wb wr wq wk bp bn bb br bq bk) destination
                newPawns' = setBit np' destination
                tHash = xorPieceAt (xorPieceAt (xorAt zHash state destination) 0 destination) 0 source `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
                (nHash, nCastle) = filteredCastlingRights (tHash, castlingRights) destination
            in
                ChessState (BitBoard newPawns' wn' wb' wr' wq' wk' bp' bn' bb' br' bq' bk') False nCastle 0 0 fullMoveclock nHash
        -- | Pawn Double Push
        applyMove' _ _ 0 0 True _ _ True = error "A double push can't be a capture"
        applyMove' source destination 0 0 False False _ True =
            let
                newPawns = clearBit wp source
                newPawns' = setBit newPawns destination
                epField = case mod destination 8 of
                    0 -> if bit (word64ToInt $ destination+1) .&. bp /= 0 then destination-8 else 0
                    7 -> if bit (word64ToInt $ destination-1) .&. bp /= 0 then destination-8 else 0
                    _ -> if (bit (word64ToInt $ destination-1) .&. bp) /= 0 || (bit (word64ToInt $ destination+1) .&. bp) /= 0 then destination-8 else 0
                nHash = xorPieceAt (xorPieceAt zHash 0 source) 0 destination `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
            in
                ChessState (BitBoard newPawns' wn wb wr wq wk bp bn bb br bq bk) False castlingRights epField 0 fullMoveclock nHash
        -- | EnPassantCapture
        applyMove' source destination 0 0 True True _ False =
            let
                newWhitePawns = clearBit wp source
                newWhitePawns' = setBit newWhitePawns destination
                newBlackPawns = clearBit bp (enPassantTarget - 8)
                nHash = xorPieceAt (xorPieceAt (xorPieceAt zHash 6 (enPassantTarget-8)) 0 destination) 0 source `xor` zBlack `xor` zEnPassant enPassantTarget
            in
                ChessState (BitBoard newWhitePawns' wn wb wr wq wk newBlackPawns bn bb br bq bk) False castlingRights 0 0 fullMoveclock nHash
        -- | Normal Pawn Promotion to Knight
        applyMove' source destination 0 1 False _ _ _ =
            let
                newPawns = clearBit wp source
                newKnights = setBit wn destination
                nHash = xorPieceAt (xorPieceAt zHash 0 source) 1 destination `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
            in
                ChessState (BitBoard newPawns newKnights wb wr wq wk bp bn bb br bq bk) False castlingRights 0 0 fullMoveclock nHash
        -- | Normal Pawn Promotion to Bishop
        applyMove' source destination 0 2 False _ _ _ =
            let
                newPawns = clearBit wp source
                newBishops = setBit wb destination
                nHash = xorPieceAt (xorPieceAt zHash 0 source) 2 destination `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
            in
                ChessState (BitBoard newPawns wn newBishops wr wq wk bp bn bb br bq bk) False castlingRights 0 0 fullMoveclock nHash
        -- | Normal Pawn Promotion to Rook
        applyMove' source destination 0 3 False _ _ _ =
            let
                newPawns = clearBit wp source
                newRooks = setBit wr destination
                nHash = xorPieceAt (xorPieceAt zHash 0 source) 3 destination `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
            in
                ChessState (BitBoard newPawns wn wb newRooks wq wk bp bn bb br bq bk) False castlingRights 0 0 fullMoveclock nHash
        -- | Normal Pawn Promotion to Queen
        applyMove' source destination 0 4 False _ _ _ =
            let
                newPawns = clearBit wp source
                newQueens = setBit wq destination
                nHash = xorPieceAt (xorPieceAt zHash 0 source) 4 destination `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
            in
                ChessState (BitBoard newPawns wn wb wr newQueens wk bp bn bb br bq bk) False castlingRights 0 0 fullMoveclock nHash
        -- | Capturing Pawn Promotion to Knight
        applyMove' source destination 0 1 True _ _ _ =
            let
                newPawns = clearBit wp source
                newKnights = setBit wn destination
                (BitBoard _ _ wb' wr' wq' wk' bp' bn' bb' br' bq' bk') = clearBits (BitBoard wp wn wb wr wq wk bp bn bb br bq bk) destination
                tHash = xorPieceAt (xorPieceAt (xorAt zHash state destination) 0 destination) 1 source `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
                (nHash, nCastle) = filteredCastlingRights (tHash, castlingRights) destination
            in
                ChessState (BitBoard newPawns newKnights wb' wr' wq' wk' bp' bn' bb' br' bq' bk') False nCastle 0 0 fullMoveclock nHash
        -- | Capturing Pawn Promotion to Bishop
        applyMove' source destination 0 2 True _ _ _ =
            let
                newPawns = clearBit wp source
                newBishops = setBit wb destination
                (BitBoard _ wn' _ wr' wq' wk' bp' bn' bb' br' bq' bk') = clearBits (BitBoard wp wn wb wr wq wk bp bn bb br bq bk) destination
                tHash = xorPieceAt (xorPieceAt (xorAt zHash state destination) 0 destination) 2 source `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
                (nHash, nCastle) = filteredCastlingRights (tHash, castlingRights) destination
            in
                ChessState (BitBoard newPawns wn' newBishops wr' wq' wk' bp' bn' bb' br' bq' bk') False nCastle 0 0 fullMoveclock nHash
        -- | Capturing Pawn Promotion to Rook
        applyMove' source destination 0 3 True _ _ _ =
            let
                newPawns = clearBit wp source
                newRooks = setBit wr destination
                (BitBoard _ wn' wb' _ wq' wk' bp' bn' bb' br' bq' bk') = clearBits (BitBoard wp wn wb wr wq wk bp bn bb br bq bk) destination
                tHash = xorPieceAt (xorPieceAt (xorAt zHash state destination) 0 destination) 3 source `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
                (nHash, nCastle) = filteredCastlingRights (tHash, castlingRights) destination
            in
                ChessState (BitBoard newPawns wn' wb' newRooks wq' wk' bp' bn' bb' br' bq' bk') False nCastle 0 0 fullMoveclock nHash
        -- | Capturing Pawn Promotion to Queen
        applyMove' source destination 0 4 True _ _ _ =
            let
                newPawns = clearBit wp source
                newQueens = setBit wq destination
                (BitBoard _ wn' wb' wr' _ wk' bp' bn' bb' br' bq' bk') = clearBits (BitBoard wp wn wb wr wq wk bp bn bb br bq bk) destination
                tHash = xorPieceAt (xorPieceAt (xorAt zHash state destination) 0 destination) 4 source `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
                (nHash, nCastle) = filteredCastlingRights (tHash, castlingRights) destination
            in
                ChessState (BitBoard newPawns wn' wb' wr' newQueens wk' bp' bn' bb' br' bq' bk') False nCastle 0 0 fullMoveclock nHash

        -- | Normal Knight Move
        applyMove' source destination 1 0 False _ _ _ =
            let
                newKnights = clearBit wn source
                newKnights' = setBit newKnights destination
                nHash = xorPieceAt (xorPieceAt zHash 1 source) 1 destination `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
            in
                ChessState (BitBoard wp newKnights' wb wr wq wk bp bn bb br bq bk) False castlingRights 0 (halfMoveClock+1) fullMoveclock nHash
        -- | Capturing Knight Move
        applyMove' source destination 1 0 True _ _ _ =
            let
                newKnights = clearBit wn source
                (BitBoard wp' wn' wb' wr' wq' wk' bp' bn' bb' br' bq' bk') = clearBits (BitBoard wp newKnights wb wr wq wk bp bn bb br bq bk) destination
                newKnights' = setBit wn' destination
                tHash = xorPieceAt (xorPieceAt (xorAt zHash state destination) 1 destination) 1 source `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
                (nHash, nCastle) = filteredCastlingRights (tHash, castlingRights) destination
            in
                ChessState (BitBoard wp' newKnights' wb' wr' wq' wk' bp' bn' bb' br' bq' bk') False nCastle 0 0 fullMoveclock nHash
        -- | Normal Bishop Move
        applyMove' source destination 2 0 False _ _ _ =
            let
                newBishops = clearBit wb source
                newBishops' = setBit newBishops destination
                nHash = xorPieceAt (xorPieceAt zHash 2 source) 2 destination `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
            in
                ChessState (BitBoard wp wn newBishops' wr wq wk bp bn bb br bq bk) False castlingRights 0 (halfMoveClock+1) fullMoveclock nHash
        -- | Capturing Bishop Move
        applyMove' source destination 2 0 True _ _ _ =
            let
                newBishops = clearBit wb source
                (BitBoard wp' wn' wb' wr' wq' wk' bp' bn' bb' br' bq' bk') = clearBits (BitBoard wp wn newBishops wr wq wk bp bn bb br bq bk) destination
                newBishops' = setBit wb' destination
                tHash = xorPieceAt (xorPieceAt (xorAt zHash state destination) 2 destination) 2 source `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
                (nHash, nCastle) = filteredCastlingRights (tHash, castlingRights) destination
            in
                ChessState (BitBoard wp' wn' newBishops' wr' wq' wk' bp' bn' bb' br' bq' bk') False nCastle 0 0 fullMoveclock nHash
        -- | Rook Moves
        -- | Normal Rook Move
        applyMove' source destination 3 0 False _ _ _ =
            let
                newRooks = clearBit wr source
                newRooks' = setBit newRooks destination
                tHash = xorPieceAt (xorPieceAt zHash 3 source) 3 destination `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
                (nHash, nCastle) = filteredCastlingRights (tHash, castlingRights) source
            in
                ChessState (BitBoard wp wn wb newRooks' wq wk bp bn bb br bq bk) False nCastle 0 (halfMoveClock+1) fullMoveclock nHash
        -- | Capturing Rook Move
        applyMove' source destination 3 0 True _ _ _ =
            let
                newRooks = clearBit wr source
                (BitBoard wp' wn' wb' wr' wq' wk' bp' bn' bb' br' bq' bk') = clearBits (BitBoard wp wn wb newRooks wq wk bp bn bb br bq bk) destination
                newRooks' = setBit wr' destination
                tHash = xorPieceAt (xorPieceAt (xorAt zHash state destination) 3 destination) 3 source `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
                (nHash, nCastle) = filteredCastlingRights (filteredCastlingRights (tHash, castlingRights) source) destination
            in
                ChessState (BitBoard wp' wn' wb' newRooks' wq' wk' bp' bn' bb' br' bq' bk') False nCastle 0 0 fullMoveclock nHash
        -- | Queen Moves
        -- | Normal Queen Move
        applyMove' source destination 4 0 False _ _ _ =
            let
                newQueens = clearBit wq source
                newQueens' = setBit newQueens destination
                nHash = xorPieceAt (xorPieceAt zHash 4 source) 4 destination `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
            in
                ChessState (BitBoard wp wn wb wr newQueens' wk bp bn bb br bq bk) False castlingRights 0 (halfMoveClock+1) fullMoveclock nHash
        -- | Capturing Queen Move
        applyMove' source destination 4 0 True _ _ _ =
            let
                newQueens = clearBit wq source
                (BitBoard wp' wn' wb' wr' wq' wk' bp' bn' bb' br' bq' bk') = clearBits (BitBoard wp wn wb wr newQueens wk bp bn bb br bq bk) destination
                newQueens' = setBit wq' destination
                tHash = xorPieceAt (xorPieceAt (xorAt zHash state destination) 4 destination) 4 source `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
                (nHash, nCastle) = filteredCastlingRights (tHash, castlingRights) destination
            in
                ChessState (BitBoard wp' wn' wb' wr' newQueens' wk' bp' bn' bb' br' bq' bk') False nCastle 0 0 fullMoveclock nHash
        -- | King Moves
        -- | Normal King Move
        applyMove' source destination 5 0 False _ False _ =
            let
                newKings = clearBit wk source
                newKings' = setBit newKings destination
                nHash = xorPieceAt (xorPieceAt zHash 5 source) 5 destination `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0) `xor` 
                    (if castlingRights .&. 0b00000001 /= 0 then zCastle 0 else 0) `xor` (if castlingRights .&. 0b00000010 /= 0 then zCastle 1 else 0)
            in
                ChessState (BitBoard wp wn wb wr wq newKings' bp bn bb br bq bk) False (castlingRights .&. 0b00001100)  0 (halfMoveClock+1) fullMoveclock nHash
        -- | Capturing King Move
        applyMove' source destination 5 0 True _ False _ =
            let
                newKings = clearBit wk source
                (BitBoard wp' wn' wb' wr' wq' wk' bp' bn' bb' br' bq' bk') = clearBits (BitBoard wp wn wb wr wq newKings bp bn bb br bq bk) destination
                newKings' = setBit wk' destination
                tHash = xorPieceAt (xorPieceAt (xorAt zHash state destination) 5 destination) 5 source `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0) `xor`
                    (if castlingRights .&. 0b00000001 /= 0 then zCastle 0 else 0) `xor` (if castlingRights .&. 0b00000010 /= 0 then zCastle 1 else 0)
                (nHash, nCastle) = filteredCastlingRights (tHash, castlingRights .&. 0b00001100) destination
            in
                ChessState (BitBoard wp' wn' wb' wr' wq' newKings' bp' bn' bb' br' bq' bk') False nCastle 0 0 fullMoveclock nHash
        -- | Castles
        -- | Queenside Castle
        applyMove' 3 5 5 0 False False True False =
            let
                newRooks = clearBit wr 7
                newRooks' = setBit newRooks 4
                newKing = clearBit wk 3
                newKing' = setBit newKing 5
                nHash = xorPieceAt (xorPieceAt (xorPieceAt (xorPieceAt zHash 5 3) 5 5) 3 7) 3 4 `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0) `xor` zCastle 0 `xor` (if castlingRights .&. 0b00000010 /= 0 then zCastle 1 else 0)
            in
                ChessState (BitBoard wp wn wb newRooks' wq newKing' bp bn bb br bq bk) False (castlingRights .&. 0b00001100) 0 (halfMoveClock+1) fullMoveclock nHash
        -- | Kingside Castle 
        applyMove' 3 1 5 0 False False True False =
            let
                newRooks = clearBit wr 0
                newRooks' = setBit newRooks 2
                newKing = clearBit wk 3
                newKing' = setBit newKing 1
                nHash = xorPieceAt (xorPieceAt (xorPieceAt (xorPieceAt zHash 5 3) 5 1) 3 0) 3 2 `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0) `xor` (if castlingRights .&. 0b00000001 /= 0 then zCastle 0 else 0) `xor` zCastle 1
            in
                ChessState (BitBoard wp wn wb newRooks' wq newKing' bp bn bb br bq bk) False (castlingRights .&. 0b00001100) 0 (halfMoveClock+1) fullMoveclock nHash
        applyMove' _ _ _ _ _ _ True _ = error "applyMove: Invalid Castle for White: "
        applyMove' _ _ 0 _ _ _ _ True = error "applyMove: Invalid double push for White: "
        applyMove' _ _ 0 _ _ _ _ _ = error "applyMove: Invalid Pawn Move for White: "
        applyMove' _ _ 1 _ _ _ _ _ = error "applyMove: Invalid Knight Move for White: "
        applyMove' _ _ 2 _ _ _ _ _ = error "applyMove: Invalid Bishop Move for White: "
        applyMove' _ _ 3 _ _ _ _ _ = error "applyMove: Invalid Rook Move for White: "
        applyMove' _ _ 4 _ _ _ _ _ = error "applyMove: Invalid Queen Move for White: "
        applyMove' _ _ 5 _ _ _ _ _ = error "applyMove: Invalid King Move for White: "



-- | Black Moves
applyMove (ChessState (BitBoard wp wn wb wr wq wk bp bn bb br bq bk) False castlingRights enPassantTarget halfMoveClock fullMoveclock zHash) move =
    let
        source = getSource move
        destination = getDestination move
        piece = getPiece move
        promotion = getPromotion move
        capture = getCapture move
        enPassant = getEnPassant move
        castle = getCastle move
        doublePush = getDoublePawnPush move
    in
        applyMove' source destination piece promotion capture enPassant castle doublePush 
    where
        state = ChessState (BitBoard wp wn wb wr wq wk bp bn bb br bq bk) True castlingRights enPassantTarget halfMoveClock fullMoveclock zHash
        -- | Pawn Moves
        -- | Normal Pawn Move
        applyMove' source destination 6 0 False False _ False =
            let
                newPawns = clearBit bp source
                newPawns' = setBit newPawns destination
                nHash = xorPieceAt (xorPieceAt zHash 6 source) 6 destination `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
            in
                ChessState (BitBoard wp wn wb wr wq wk newPawns' bn bb br bq bk) True castlingRights 0 (halfMoveClock+1) (fullMoveclock+1) nHash
        -- | Normal Pawn Capture
        applyMove' source destination 6 0 True False _ False =
            let
                newPawns = clearBit bp source
                (BitBoard wp' wn' wb' wr' wq' wk' bp' bn' bb' br' bq' bk') = clearBits (BitBoard wp wn wb wr wq wk newPawns bn bb br bq bk) destination
                newPawns' = setBit bp' destination
                tHash = xorPieceAt (xorPieceAt (xorAt zHash state destination) 6 destination) 6 source `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
                (nHash, nCastle) = filteredCastlingRights (tHash, castlingRights) destination
            in
                ChessState (BitBoard wp' wn' wb' wr' wq' wk' newPawns' bn' bb' br' bq' bk') True nCastle 0 0 (fullMoveclock+1) nHash
        -- | En Passant Capture
        applyMove' source destination 6 0 True True False _ =
            let
                newBlackPawns = clearBit bp source
                newBlackPawns' = setBit newBlackPawns destination
                newWhitePawns = clearBit wp (enPassantTarget + 8)
                nHash = xorPieceAt (xorPieceAt (xorPieceAt zHash 0 (enPassantTarget+8)) 6 destination) 6 source `xor` zBlack `xor` zEnPassant enPassantTarget
            in
                ChessState (BitBoard newWhitePawns wn wb wr wq wk newBlackPawns' bn bb br bq bk) True castlingRights 0 0 (fullMoveclock+1) nHash
        -- | Double Pawn Push
        applyMove' source destination 6 0 False False False True =
            let
                newPawns = clearBit bp source
                newPawns' = setBit newPawns destination
                epField = case mod destination 8 of
                    0 -> if bit (word64ToInt $ destination+1) .&. wp /= 0 then destination+8 else 0
                    7 -> if bit (word64ToInt $ destination-1) .&. wp /= 0 then destination+8 else 0
                    _ -> if (bit (word64ToInt $ destination-1) .&. wp) /= 0 || (bit (word64ToInt $ destination+1) .&. wp) /= 0 then destination+8 else 0
                nHash = xorPieceAt (xorPieceAt zHash 0 source) 0 destination `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
            in
                ChessState (BitBoard wp wn wb wr wq wk newPawns' bn bb br bq bk) True castlingRights epField (halfMoveClock+1) (fullMoveclock+1) nHash
        -- | Normal Pawn Promotion to Knight
        applyMove' source destination 6 7 False False _ False =
            let
                newPawns = clearBit bp source
                newKnights = setBit bn destination
                nHash = xorPieceAt (xorPieceAt zHash 6 source) 7 destination `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
            in
                ChessState (BitBoard wp wn wb wr wq wk newPawns newKnights bb br bq bk) True castlingRights 0 0 (fullMoveclock+1) nHash
        -- | Normal Pawn Promotion to Bishop
        applyMove' source destination 6 8 False False _ False =
            let
                newPawns = clearBit bp source
                newBishops = setBit bb destination
                nHash = xorPieceAt (xorPieceAt zHash 6 source) 8 destination `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
            in
                ChessState (BitBoard wp wn wb wr wq wk newPawns bn newBishops br bq bk) True castlingRights 0 0 (fullMoveclock+1) nHash
        -- | Normal Pawn Promotion to Rook
        applyMove' source destination 6 9 False False _ False =
            let
                newPawns = clearBit bp source
                newRooks = setBit br destination
                nHash = xorPieceAt (xorPieceAt zHash 6 source) 9 destination `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
            in
                ChessState (BitBoard wp wn wb wr wq wk newPawns bn bb newRooks bq bk) True castlingRights 0 0 (fullMoveclock+1) nHash
        -- | Normal Pawn Promotion to Queen
        applyMove' source destination 6 10 False False _ False =
            let
                newPawns = clearBit bp source
                newQueens = setBit bq destination
                nHash = xorPieceAt (xorPieceAt zHash 6 source) 11 destination `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
            in
                ChessState (BitBoard wp wn wb wr wq wk newPawns bn bb br newQueens bk) True castlingRights 0 0 (fullMoveclock+1) nHash
        -- | Capturing Pawn Promotion to Knight
        applyMove' source destination 6 7 True False _ False =
            let
                newPawns = clearBit bp source
                newKnights = setBit bn destination
                (BitBoard wp' wn' wb' wr' wq' wk' _ _ bb' br' bq' bk') = clearBits (BitBoard wp wn wb wr wq wk newPawns bn bb br bq bk) destination
                tHash = xorPieceAt (xorPieceAt (xorAt zHash state destination) 6 destination) 7 source `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
                (nHash, nCastle) = filteredCastlingRights (tHash, castlingRights) destination
            in
                ChessState (BitBoard wp' wn' wb' wr' wq' wk' newPawns newKnights bb' br' bq' bk') True nCastle 0 0 (fullMoveclock+1) nHash
        -- | Capturing Pawn Promotion to Bishop
        applyMove' source destination 6 8 True False _ False =
            let
                newPawns = clearBit bp source
                newBishops = setBit bb destination
                (BitBoard wp' wn' wb' wr' wq' wk' _ bn' _' br' bq' bk') = clearBits (BitBoard wp wn wb wr wq wk newPawns bn bb br bq bk) destination
                tHash = xorPieceAt (xorPieceAt (xorAt zHash state destination) 6 destination) 8 source `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
                (nHash, nCastle) = filteredCastlingRights (tHash, castlingRights) destination
            in
                ChessState (BitBoard wp' wn' wb' wr' wq' wk' newPawns bn' newBishops br' bq' bk') True nCastle 0 0 (fullMoveclock+1) nHash
        -- | Capturing Pawn Promotion to Rook
        applyMove' source destination 6 9 True False _ False =
            let
                newPawns = clearBit bp source
                newRooks = setBit br destination
                (BitBoard wp' wn' wb' wr' wq' wk' _ bn' bb' _ bq' bk') = clearBits (BitBoard wp wn wb wr wq wk newPawns bn bb br bq bk) destination
                tHash = xorPieceAt (xorPieceAt (xorAt zHash state destination) 6 destination) 9 source `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
                (nHash, nCastle) = filteredCastlingRights (tHash, castlingRights) destination
            in
                ChessState (BitBoard wp' wn' wb' wr' wq' wk' newPawns bn' bb' newRooks bq' bk') True nCastle 0 0 (fullMoveclock+1) nHash
        -- | Capturing Pawn Promotion to Queen
        applyMove' source destination 6 10 True False _ False =
            let
                newPawns = clearBit bp source
                newQueens = setBit bq destination
                (BitBoard wp' wn' wb' wr' wq' wk' _ bn' bb' br' _ bk') = clearBits (BitBoard wp wn wb wr wq wk newPawns bn bb br bq bk) destination
                tHash = xorPieceAt (xorPieceAt (xorAt zHash state destination) 6 destination) 10 source `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
                (nHash, nCastle) = filteredCastlingRights (tHash, castlingRights) destination
            in
                ChessState (BitBoard wp' wn' wb' wr' wq' wk' newPawns bn' bb' br' newQueens bk') True nCastle 0 0 (fullMoveclock+1) nHash

        -- | Knight Moves
        -- | Normal Knight Move
        applyMove' source destination 7 0 False False _ False =
            let
                newKnights = setBit bn destination
                newKnights' = clearBit newKnights source
                nHash = xorPieceAt (xorPieceAt zHash 7 source) 7 destination `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
            in
                ChessState (BitBoard wp wn wb wr wq wk bp newKnights' bb br bq bk) True castlingRights 0 (halfMoveClock+1) (fullMoveclock+1) nHash
        -- | Capturing Knight Move
        applyMove' source destination 7 0 True False _ False =
            let
                newKnights = clearBit bn source
                (BitBoard wp' wn' wb' wr' wq' wk' bp' bn' bb' br' bq' bk') = clearBits (BitBoard wp wn wb wr wq wk bp newKnights bb br bq bk) destination
                newKnights' = setBit bn' destination
                tHash = xorPieceAt (xorPieceAt (xorAt zHash state destination) 7 destination) 7 source `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
                (nHash, nCastle) = filteredCastlingRights (tHash, castlingRights) destination
            in
                ChessState (BitBoard wp' wn' wb' wr' wq' wk' bp' newKnights' bb' br' bq' bk') True nCastle 0 0 (fullMoveclock+1) nHash

        -- | Bishop Moves
        -- | Normal Bishop Move
        applyMove' source destination 8 0 False False _ False =
            let
                newBishops = setBit bb destination
                newBishops' = clearBit newBishops source
                nHash = xorPieceAt (xorPieceAt zHash 8 source) 8 destination `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
            in
                ChessState (BitBoard wp wn wb wr wq wk bp bn newBishops' br bq bk) True castlingRights 0 (halfMoveClock+1) (fullMoveclock+1) nHash
        -- | Capturing Bishop Move
        applyMove' source destination 8 0 True False _ False =
            let
                newBishops = clearBit bb source
                (BitBoard wp' wn' wb' wr' wq' wk' bp' bn' bb' br' bq' bk') = clearBits (BitBoard wp wn wb wr wq wk bp bn newBishops br bq bk) destination
                newBishops' = setBit bb' destination
                tHash = xorPieceAt (xorPieceAt (xorAt zHash state destination) 8 destination) 8 source `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
                (nHash, nCastle) = filteredCastlingRights (tHash, castlingRights) destination
            in
                ChessState (BitBoard wp' wn' wb' wr' wq' wk' bp' bn' newBishops' br' bq' bk') True nCastle 0 0 (fullMoveclock+1) nHash

        -- | Rook Moves
        -- | Normal Rook Move
        applyMove' source destination 9 0 False False _ False =
            let
                newRooks = setBit br destination
                newRooks' = clearBit newRooks source
                tHash = xorPieceAt (xorPieceAt zHash 9 source) 9 destination `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
                (nHash, nCastle) = filteredCastlingRights (tHash, castlingRights) source
            in
                ChessState (BitBoard wp wn wb wr wq wk bp bn bb newRooks' bq bk) True nCastle 0 (halfMoveClock+1) (fullMoveclock+1) nHash
        -- | Capturing Rook Move
        applyMove' source destination 9 0 True False _ False =
            let
                newRooks = clearBit br source
                (BitBoard wp' wn' wb' wr' wq' wk' bp' bn' bb' br' bq' bk') = clearBits (BitBoard wp wn wb wr wq wk bp bn bb newRooks bq bk) destination
                newRooks' = setBit br' destination
                tHash = xorPieceAt (xorPieceAt (xorAt zHash state destination) 9 destination) 9 source `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
                (nHash, nCastle) = filteredCastlingRights (filteredCastlingRights (tHash, castlingRights) source) destination
            in
                ChessState (BitBoard wp' wn' wb' wr' wq' wk' bp' bn' bb' newRooks' bq' bk') True nCastle 0 0 (fullMoveclock+1) nHash

        -- | Queen Moves
        -- | Normal Queen Move
        applyMove' source destination 10 0 False False _ False =
            let
                newQueens = setBit bq destination
                newQueens' = clearBit newQueens source
                nHash = xorPieceAt (xorPieceAt zHash 10 source) 10 destination `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
            in
                ChessState (BitBoard wp wn wb wr wq wk bp bn bb br newQueens' bk) True castlingRights 0 (halfMoveClock+1) (fullMoveclock+1) nHash
        -- | Capturing Queen Move
        applyMove' source destination 10 0 True False _ False =
            let
                newQueens = clearBit bq source
                (BitBoard wp' wn' wb' wr' wq' wk' bp' bn' bb' br' bq' bk') = clearBits (BitBoard wp wn wb wr wq wk bp bn bb br newQueens bk) destination
                newQueens' = setBit bq' destination
                tHash = xorPieceAt (xorPieceAt (xorAt zHash state destination) 10 destination) 10 source `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0)
                (nHash, nCastle) = filteredCastlingRights (tHash, castlingRights) destination
            in
                ChessState (BitBoard wp' wn' wb' wr' wq' wk' bp' bn' bb' br' newQueens' bk') True nCastle 0 0 (fullMoveclock+1) nHash

        -- | King Moves
        -- | Normal King Move
        applyMove' source destination 11 0 False False False False =
            let
                newKing = setBit bk destination
                newKing' = clearBit newKing source
                nHash = xorPieceAt (xorPieceAt zHash 11 source) 11 destination `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0) `xor` 
                    (if castlingRights .&. 0b00000100 /= 0 then zCastle 2 else 0) `xor` (if castlingRights .&. 0b00001000 /= 0 then zCastle 3 else 0)
            in
                ChessState (BitBoard wp wn wb wr wq wk bp bn bb br bq newKing') True (castlingRights .&. 0b00000011) 0 (halfMoveClock+1) (fullMoveclock+1) nHash
        -- | Capturing King Move
        applyMove' source destination 11 0 True False False False =
            let
                newKing = clearBit bk source
                (BitBoard wp' wn' wb' wr' wq' wk' bp' bn' bb' br' bq' bk') = clearBits (BitBoard wp wn wb wr wq wk bp bn bb br bq newKing) destination
                newKing' = setBit bk' destination
                tHash = xorPieceAt (xorPieceAt (xorAt zHash state destination) 11 destination) 11 source `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0) `xor`
                    (if castlingRights .&. 0b00000100 /= 0 then zCastle 2 else 0) `xor` (if castlingRights .&. 0b00001000 /= 0 then zCastle 3 else 0)
                (nHash, nCastle) = filteredCastlingRights (tHash, castlingRights .&. 0b00000011) destination
            in
                ChessState (BitBoard wp' wn' wb' wr' wq' wk' bp' bn' bb' br' bq' newKing') True nCastle 0 0 (fullMoveclock+1) nHash

        -- | Castling Moves
        -- | Queenside Castling
        applyMove' 59 61 11 0 False False True False =
            let
                newRooks = clearBit br 63
                newRooks' = setBit newRooks 60
                newKing = clearBit bk 59
                newKing' = setBit newKing 61
                nHash = xorPieceAt (xorPieceAt (xorPieceAt (xorPieceAt zHash 11 59) 11 61) 9 63) 9 50 `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0) `xor` zCastle 2 `xor` (if castlingRights .&. 0b00001000 /= 0 then zCastle 3 else 0)
            in
                ChessState (BitBoard wp wn wb wr wq wk bp bn bb newRooks' bq newKing') True (castlingRights .&. 0b00000011) 0 (halfMoveClock+1) (fullMoveclock+1) nHash
        -- | Kingside Castling
        applyMove' 59 57 11 0 False False True False =
            let
                newRooks = clearBit br 56
                newRooks' = setBit newRooks 58
                newKing = clearBit bk 59
                newKing' = setBit newKing 57
                nHash = xorPieceAt (xorPieceAt (xorPieceAt (xorPieceAt zHash 11 59) 11 57) 9 56) 9 58 `xor` zBlack `xor` (if enPassantTarget /= 0 then zEnPassant enPassantTarget else 0) `xor` (if castlingRights .&. 0b00000100 /= 0 then zCastle 2 else 0) `xor` zCastle 3
            in
                ChessState (BitBoard wp wn wb wr wq wk bp bn bb newRooks' bq newKing') True (castlingRights .&. 0b00000011) 0 (halfMoveClock+1) (fullMoveclock+1) nHash
        applyMove' _ _ _ _ _ _ True _ = error "applyMove: Invalid Castling Move for Black"
        applyMove' _ _ 6 _ _ _ _ True = error "applyMove: Invalid double push for Black"
        applyMove' _ _ 6 _ _ _ _ _ = error "applyMove: Invalid Pawn Move for Black"
        applyMove' _ _ 7 _ _ _ _ _ = error "applyMove: Invalid Knight Move for Black"
        applyMove' _ _ 8 _ _ _ _ _ = error "applyMove: Invalid Bishop Move for Black"
        applyMove' _ _ 9 _ _ _ _ _ = error "applyMove: Invalid Rook Move for Black"
        applyMove' _ _ 10 _ _ _ _ _ = error "applyMove: Invalid Queen Move for Black"
        applyMove' _ _ 11 _ _ _ _ _ = error "applyMove: Invalid King Move for Black"

