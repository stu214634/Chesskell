{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-type-defaults #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE  BinaryLiterals #-}

module MoveGeneration where
import Model(BitBoard (BitBoard), Move, ChessState (ChessState), getDestination)
import Data.Word (Word64)
import MoveApplication (getWhitePieces, getBlackPieces, getAllPieces, applyMove, getPieceBits)
import Data.Bits (Bits(unsafeShiftL, (.|.), unsafeShiftR, (.&.), bit, complement), FiniteBits (countTrailingZeros))
import BitMasks (genColMasks, lastBits, rookTable, bishopTable, kingTable, knightTable)
import BitFuncs (popLSB, intToWord64, word64ToInt)

$genColMasks

pUpMask :: Word64 -> Word64
pUpMask n
    | n < 8 =  0xFFFFFFFFFFFFFF00
    | n < 16 = 0xFFFFFFFFFFFF0000
    | n < 24 = 0xFFFFFFFFFF000000
    | n < 32 = 0xFFFFFFFF00000000
    | n < 40 = 0xFFFFFF0000000000
    | n < 48 = 0xFFFF000000000000
    | otherwise = 0xFF00000000000000

pDownMask :: Word64 -> Word64
pDownMask n
    | n >= 56 = 0x00FFFFFFFFFFFFFF
    | n >= 48 = 0x0000FFFFFFFFFFFF
    | n >= 40 = 0x000000FFFFFFFFFF
    | n >= 32 = 0x00000000FFFFFFFF
    | n >= 24 = 0x0000000000FFFFFF
    | n >= 16 = 0x000000000000FFFF
    | otherwise =  0x00000000000000FF

pLeftMask :: Word64 -> Word64
pLeftMask n = case mod n 8 of
    0 -> colMask11111110
    1 -> colMask11111100
    2 -> colMask11111000
    3 -> colMask11110000
    4 -> colMask11100000
    5 -> colMask11000000
    6 -> colMask10000000
    _ -> 0

pRightMask :: Word64 -> Word64
pRightMask n = case mod n 8 of
    7 -> colMask01111111
    6 -> colMask00111111
    5 -> colMask00011111
    4 -> colMask00001111
    3 -> colMask00000111
    2 -> colMask00000011
    1 -> colMask00000001
    _ -> 0

pUpLeftMask :: Word64 -> Word64
pUpLeftMask n = pUpMask n .&. pLeftMask n
pUpRightMask :: Word64 -> Word64
pUpRightMask n = pUpMask n .&. pRightMask n
pDownLeftMask :: Word64 -> Word64
pDownLeftMask n = pDownMask n .&. pLeftMask n
pDownRightMask :: Word64 -> Word64
pDownRightMask n = pDownMask n .&. pRightMask n

-- | Bitmasks for covered squares
-- | Up
upMask :: BitBoard -> Bool -> Word64 -> Word64
{-# INLINE upMask #-}
upMask b w p = let pieces = pUpMask p .&. getAllPieces b
                   mPieces = pUpMask p .&. (if w then getWhitePieces else getBlackPieces) b
                in mPieces .|. (pieces `unsafeShiftL` 8) .|. (pieces `unsafeShiftL` 16) .|. (pieces `unsafeShiftL` 24) .|. (pieces `unsafeShiftL` 32) .|. (pieces `unsafeShiftL` 40) .|. (pieces `unsafeShiftL` 48) .|. (pieces `unsafeShiftL` 56)
-- | Down
downMask :: BitBoard -> Bool -> Word64 -> Word64
{-# INLINE downMask #-}
downMask b w p = let pieces = pDownMask p .&. getAllPieces b
                     mPieces = pDownMask p .&. (if w then getWhitePieces else getBlackPieces) b
                in mPieces .|. (pieces `unsafeShiftR` 8) .|. (pieces `unsafeShiftR` 16) .|. (pieces `unsafeShiftR` 24) .|. (pieces `unsafeShiftR` 32) .|. (pieces `unsafeShiftR` 40) .|. (pieces `unsafeShiftR` 48) .|. (pieces `unsafeShiftR` 56)
-- | Left
leftMask :: BitBoard -> Bool -> Word64 -> Word64
{-# INLINE leftMask #-}
leftMask b w p = let pieces = pLeftMask p .&. getAllPieces b
                     mPieces = pLeftMask p .&. (if w then getWhitePieces else getBlackPieces) b
                in mPieces .|. ((pieces .&. colMask01111111) `unsafeShiftL` 1)
                .|. ((pieces .&. colMask00111111) `unsafeShiftL` 2)
                .|. ((pieces .&. colMask00011111) `unsafeShiftL` 3)
                .|. ((pieces .&. colMask00001111) `unsafeShiftL` 4)
                .|. ((pieces .&. colMask00000111) `unsafeShiftL` 5)
                .|. ((pieces .&. colMask00000011) `unsafeShiftL` 6)
-- | Right
rightMask :: BitBoard -> Bool -> Word64 -> Word64
{-# INLINE rightMask #-}
rightMask b w p = let pieces = pRightMask p .&. getAllPieces b
                      mPieces = pRightMask p .&. (if w then getWhitePieces else getBlackPieces) b
                in mPieces .|.  ((pieces .&. colMask11111110) `unsafeShiftR` 1)
                .|. ((pieces .&. colMask11111100) `unsafeShiftR` 2)
                .|. ((pieces .&. colMask11111000) `unsafeShiftR` 3)
                .|. ((pieces .&. colMask11110000) `unsafeShiftR` 4)
                .|. ((pieces .&. colMask11100000) `unsafeShiftR` 5)
                .|. ((pieces .&. colMask11000000) `unsafeShiftR` 6)
-- | Up-Left
upLeftMask :: BitBoard -> Bool -> Word64 -> Word64
{-# INLINE upLeftMask #-}
upLeftMask b w p = let pieces = pUpLeftMask p .&. getAllPieces b
                       mPieces = pUpLeftMask p .&. (if w then getWhitePieces else getBlackPieces) b
                 in mPieces .|. ((pieces .&. colMask01111111) `unsafeShiftL` 9)
                .|. ((pieces .&. colMask00111111) `unsafeShiftL` 18)
                .|. ((pieces .&. colMask00011111) `unsafeShiftL` 27)
                .|. ((pieces .&. colMask00001111) `unsafeShiftL` 36)
                .|. ((pieces .&. colMask00000111) `unsafeShiftL` 45)
                .|. ((pieces .&. colMask00000011) `unsafeShiftL` 54)
-- | Down-Left
downLeftMask :: BitBoard -> Bool -> Word64 -> Word64
{-# INLINE downLeftMask #-}
downLeftMask b w p = let pieces = pDownLeftMask p .&. getAllPieces b
                         mPieces = pDownLeftMask p .&. (if w then getWhitePieces else getBlackPieces) b
                in mPieces .|.  ((pieces .&. colMask01111111) `unsafeShiftR` 7)
                .|. ((pieces .&. colMask00111111) `unsafeShiftR` 14)
                .|. ((pieces .&. colMask00011111) `unsafeShiftR` 21)
                .|. ((pieces .&. colMask00001111) `unsafeShiftR` 28)
                .|. ((pieces .&. colMask00000111) `unsafeShiftR` 35)
                .|. ((pieces .&. colMask00000011) `unsafeShiftR` 42)
-- | Up-Right
upRightMask :: BitBoard -> Bool -> Word64 -> Word64
{-# INLINE upRightMask #-}
upRightMask b w p = let pieces = pUpRightMask p .&. getAllPieces b
                        mPieces = pUpRightMask p .&. (if w then getWhitePieces else getBlackPieces) b
                in mPieces .|. ((pieces .&. colMask11111110) `unsafeShiftL` 7)
                .|. ((pieces .&. colMask11111100) `unsafeShiftL` 14)
                .|. ((pieces .&. colMask11111000) `unsafeShiftL` 21)
                .|. ((pieces .&. colMask11110000) `unsafeShiftL` 28)
                .|. ((pieces .&. colMask11100000) `unsafeShiftL` 35)
                .|. ((pieces .&. colMask11000000) `unsafeShiftL` 42)
-- | Down-Right
downRightMask :: BitBoard -> Bool -> Word64 -> Word64
{-# INLINE downRightMask #-}
downRightMask b w p = let pieces = pDownRightMask p .&. getAllPieces b
                          mPieces = pDownRightMask p .&. (if w then getWhitePieces else getBlackPieces) b
                in mPieces .|.  ((pieces .&. colMask11111110) `unsafeShiftR` 9)
                .|. ((pieces .&. colMask11111100) `unsafeShiftR` 18)
                .|. ((pieces .&. colMask11111000) `unsafeShiftR` 27)
                .|. ((pieces .&. colMask11110000) `unsafeShiftR` 36)
                .|. ((pieces .&. colMask11100000) `unsafeShiftR` 45)
                .|. ((pieces .&. colMask11000000) `unsafeShiftR` 54)


genAllMoves :: ChessState -> Bool -> Bool -> [Move]
genAllMoves (ChessState (BitBoard wpT wnT wbT wrT wqT wkT bpT bnT bbT brT bqT bkT) True castles enPassantField _ _ _) threats capturesOnly =
    if not threats && not capturesOnly then [(1 `unsafeShiftL` 24) .|. (5 `unsafeShiftL` 14) .|. (d `unsafeShiftL` 7) .|. 3| (c, f, tf, d) <- [(1, 0x0000000000000006, 0x000000000000000E, 1), (2, 0x0000000000000070, 0x0000000000000038, 5)], castles .&. c /= 0, (allPieces .&. f) == 0, (enemyThreatens .&. tf) == 0]
                    ++ concatMap (genMoves b) [0..5]
    else concatMap (genMoves b) [0..5]
    where
    enemyThreatens = foldl (\acc m -> acc .|. bit (word64ToInt $ getDestination m)) (0 :: Word64) $ genAllMoves (ChessState (BitBoard wpT wnT wbT wrT wqT wkT bpT bnT bbT brT bqT bkT) False castles 0 0 0 0) True False
    allPieces = getAllPieces (BitBoard wpT wnT wbT wrT wqT wkT bpT bnT bbT brT bqT bkT)
    b = BitBoard wpT wnT wbT wrT wqT wkT bpT bnT bbT brT bqT bkT
    completeMoves :: Word64 -> Word64 -> Word64 -> [Move]
    completeMoves _ _ 0 = []
    completeMoves p s d = let (destination, rest) = popLSB d
                              capture = intToWord64 $ if (bit (word64ToInt destination) .&. allPieces) /= 0 then 1 else 0
                          in
                            if not capturesOnly || (capture /= 0 ) then ((capture `unsafeShiftL` 22) .|. ( p `unsafeShiftL` 14) .|. ( destination `unsafeShiftL` 7) .|.  s) : completeMoves p s rest
                            else completeMoves p s rest

    pawnForwardWhite :: Word64 -> Word64 -> [Move]
    pawnForwardWhite _ 0 = []
    pawnForwardWhite s d = if s >= 48
        then [( p `unsafeShiftL` 18) .|. (intToWord64 (countTrailingZeros d) `unsafeShiftL` 7) .|.  s | p <- [1, 2, 3, 4]]
        else ((intToWord64 (countTrailingZeros d) `unsafeShiftL` 7) .|.  s) :
        let pushDest = (d `unsafeShiftL` 8) in [(1 `unsafeShiftL` 25) .|. (intToWord64 (countTrailingZeros pushDest) `unsafeShiftL` 7) .|.  s | s < 16, pushDest .&. allPieces == 0]

    pawnCaptureWhite :: Word64 -> Word64 -> [Move]
    pawnCaptureWhite _ 0 = []
    pawnCaptureWhite s d = let (destination, rest) = popLSB d in
        (if s >= 48
        then [$([|(1 `unsafeShiftL` 22)|]) .|. ( p `unsafeShiftL` 18) .|. ( destination `unsafeShiftL` 7) .|.  s | p <- [1, 2, 3, 4]]
        else [$([|(1 `unsafeShiftL` 22)|]) .|. ( destination `unsafeShiftL` 7) .|.  s])
        ++ pawnCaptureWhite s rest

    genMoves :: BitBoard -> Word64 -> [Move]
    genMoves (BitBoard wp _ _ _ _ _ _ _ _ _ _ _) 0 = case wp of
        0 -> []
        n -> let (source, restPawns) = popLSB n in
            (if enPassantField /= 0 && not threats then
            [$([|(3 `unsafeShiftL` 22)|]) .|. ( enPassantField `unsafeShiftL` 7) .|.  source  | enPassantField == source + 9 && not (source == 31 && enPassantField == 40)] ++
            [$([|(3 `unsafeShiftL` 22)|]) .|. ( enPassantField `unsafeShiftL` 7) .|.  source  | enPassantField == source + 7]
            else [])
            ++ pawnCaptureWhite source (let sBit = bit (word64ToInt source) in (((sBit `unsafeShiftL` 7) .&. colMask01111111) .|. ((sBit `unsafeShiftL` 9) .&. colMask11111110)) .&. if not threats then getBlackPieces b else 0xFFFFFFFFFFFFFFFF)
            ++ (if not threats && not capturesOnly then pawnForwardWhite source ((bit (word64ToInt source) `unsafeShiftL` 8) .&. complement allPieces) else [])
            ++ genMoves (BitBoard restPawns 0 0 0 0 0 0 0 0 0 0 0) 0

    genMoves (BitBoard _ wn _ _ _ _ _ _ _ _ _ _) 1 =  case wn of
        0 -> []
        n -> let (source, restKnights) = popLSB n in
            completeMoves 1 source (complement (getWhitePieces b) .&. knightTable source)
            ++ genMoves (BitBoard wpT restKnights wbT wrT wqT wkT bpT bnT bbT brT bqT bkT) 1

    genMoves (BitBoard _ _ wb _ _ _ _ _ _ _ _ _) 2 = case wb of
        0 -> []
        n -> let (source, restBishops) = popLSB n in
            completeMoves 2 source (complement (upLeftMask b True source .|. upRightMask b True source .|. downLeftMask b True source .|. downRightMask b True source) .&. bishopTable source)
            ++ genMoves (BitBoard wpT wnT restBishops wrT wqT wkT bpT bnT bbT brT bqT bkT) 2

    genMoves (BitBoard _ _ _ wr _ _ _ _ _ _ _ _) 3 = case wr of
        0 -> []
        n -> let (source, restRooks) = popLSB n in
            completeMoves 3 source (complement (leftMask b True source .|. rightMask b True source .|. upMask b True source .|. downMask b True source) .&. rookTable source)
            ++ genMoves (BitBoard wpT wnT wbT restRooks wqT wkT bpT bnT bbT brT bqT bkT) 3

    genMoves (BitBoard _ _ _ _ wq _ _ _ _ _ _ _) 4 = case wq of
        0 -> []
        n -> let (source, restQueens) = popLSB n in
            completeMoves 4 source ((complement (leftMask b True source .|. rightMask b True source .|. upMask b True source .|. downMask b True source) .&. rookTable source)
                                .|. (complement (upLeftMask b True source .|. upRightMask b True source .|. downLeftMask b True source .|. downRightMask b True source) .&. bishopTable source))
            ++ genMoves (BitBoard wpT wnT wbT wrT restQueens wkT bpT bnT bbT brT bqT bkT) 4

    genMoves (BitBoard _ _ _ _ _ wk _ _ _ _ _ _) 5 =  let (source, _) = popLSB wk in
            completeMoves 5 source (complement (getWhitePieces b) .&. kingTable source)

    genMoves _ _ = error "genMoves: invalid piece for white"

genAllMoves (ChessState (BitBoard wpT wnT wbT wrT wqT wkT bpT bnT bbT brT bqT bkT) False castles enPassantField _ _ _) threats capturesOnly =
    if not threats then [(1 `unsafeShiftL` 24) .|. (11 `unsafeShiftL` 14) .|. (d `unsafeShiftL` 7) .|. 59| (c, f, tf, d) <- [(4, 0x0600000000000000, 0x0E00000000000000, 57), (8, 0x7000000000000000, 0x3800000000000000, 61)], castles .&. c /= 0, (allPieces .&. f) == 0, (enemyThreatens .&. tf) == 0]
                    ++ concatMap (genMoves b) [6..11]
    else concatMap (genMoves b) [6..11]
    where
    enemyThreatens = foldl (\acc m -> acc .|. bit (word64ToInt $ getDestination m)) (0 :: Word64) $ genAllMoves (ChessState (BitBoard wpT wnT wbT wrT wqT wkT bpT bnT bbT brT bqT bkT) True castles 0 0 0 0) True False
    allPieces = getAllPieces b
    b = BitBoard wpT wnT wbT wrT wqT wkT bpT bnT bbT brT bqT bkT

    completeMoves :: Word64 -> Word64 -> Word64 -> [Move]
    completeMoves _ _ 0 = []
    completeMoves p s d = let (destination, rest) = popLSB d
                              capture = intToWord64 $ if (bit (word64ToInt destination) .&. allPieces) /= 0 then 1 else 0
                          in
                              if not capturesOnly || (capture /= 0) then ((capture `unsafeShiftL` 22) .|. ( p `unsafeShiftL` 14) .|. ( destination `unsafeShiftL` 7) .|.  s) : completeMoves p s rest
                              else completeMoves p s rest

    pawnForwardBlack :: Word64 -> Word64 -> [Move]
    pawnForwardBlack _ 0 = []
    pawnForwardBlack s d = if s <= 15
        then [( p `unsafeShiftL` 18) .|. $([|(6 `unsafeShiftL` 14)|]) .|. (intToWord64 (countTrailingZeros d) `unsafeShiftL` 7) .|.  s | p <- [7, 8, 9, 10]]
        else ($([|(6 `unsafeShiftL` 14)|]) .|. (intToWord64 (countTrailingZeros d) `unsafeShiftL` 7) .|.  s) :
        let pushDest = (d `unsafeShiftR` 8) in [(1 `unsafeShiftL` 25) .|. $([|(6 `unsafeShiftL` 14)|]) .|. (intToWord64 (countTrailingZeros pushDest) `unsafeShiftL` 7) .|.  s | s > 47, pushDest .&. allPieces == 0]

    pawnCaptureBlack :: Word64 -> Word64 -> [Move]
    pawnCaptureBlack _ 0 = []
    pawnCaptureBlack s d = let (destination, rest) = popLSB d in
        (if s <= 15
        then [$([|(1 `unsafeShiftL` 22)|]) .|. ( p `unsafeShiftL` 18) .|. $([|(6 `unsafeShiftL` 14)|]) .|. ( destination `unsafeShiftL` 7) .|.  s | p <- [7, 8, 9, 10]]
        else [$([|(1 `unsafeShiftL` 22)|]) .|. $([|(6 `unsafeShiftL` 14)|]) .|. ( destination `unsafeShiftL` 7) .|.  s]) ++ pawnCaptureBlack s rest

    genMoves (BitBoard _ _ _ _ _ _ bp _ _ _ _ _) 6 = case bp of
        0 -> []
        n -> let (source, restPawns) = popLSB n in
            (if enPassantField /= 0 && not threats then
            [$([|(3 `unsafeShiftL` 22)|]) .|. $([|(6 `unsafeShiftL` 14)|]) .|. ( enPassantField `unsafeShiftL` 7) .|.  source  | enPassantField == source - 9 && not (source == 32 && enPassantField == 23)] ++
            [$([|(3 `unsafeShiftL` 22)|]) .|. $([|(6 `unsafeShiftL` 14)|]) .|. ( enPassantField `unsafeShiftL` 7) .|.  source  | enPassantField == source - 7]
            else [])
            ++ pawnCaptureBlack source (let sBit = bit (word64ToInt source) in (((sBit `unsafeShiftR` 9) .&. colMask01111111) .|. ((sBit `unsafeShiftR` 7) .&. colMask11111110)) .&. if not threats then getWhitePieces b else 0xFFFFFFFFFFFFFFFF)
            ++ (if not threats && not capturesOnly then pawnForwardBlack source ((bit (word64ToInt source) `unsafeShiftR` 8) .&. complement allPieces) else [])
            ++ genMoves (BitBoard 0 0 0 0 0 0 restPawns 0 0 0 0 0) 6

    genMoves (BitBoard _ _ _ _ _ _ _ bn _ _ _ _) 7 =  case bn of
        0 -> []
        n -> let (source, restKnights) = popLSB n in
            completeMoves 7 source (complement (getBlackPieces b) .&. knightTable source)
            ++ genMoves (BitBoard wpT wkT wbT wrT wqT wkT bpT restKnights bbT brT bqT bkT) 7

    genMoves (BitBoard _ _ _ _ _ _ _ _ bb _ _ _) 8 = case bb of
        0 -> []
        n -> let (source, restBishops) = popLSB n in
            completeMoves 8 source (complement (upLeftMask b False source .|. upRightMask b False source .|. downLeftMask b False source .|. downRightMask b False source) .&. bishopTable source)
            ++ genMoves (BitBoard wpT wnT wbT wrT wqT wkT bpT bnT restBishops brT bqT bkT) 8

    genMoves (BitBoard _ _ _ _ _ _ _ _ _ br _ _) 9 = case br of
        0 -> []
        n -> let (source, restRooks) = popLSB n in
            completeMoves 9 source (complement (leftMask b False source .|. rightMask b False source .|. upMask b False source .|. downMask b False source) .&. rookTable source)
            ++ genMoves (BitBoard wpT wnT wbT wrT wqT wkT bpT bnT bbT restRooks bqT bkT) 9

    genMoves (BitBoard _ _ _ _ _ _ _ _ _ _ bq _) 10 = case bq of
        0 -> []
        n -> let (source, restQueens) = popLSB n in
            completeMoves 10 source ((complement (leftMask b False source .|. rightMask b False source .|. upMask b False source .|. downMask b False source) .&. rookTable source)
                                .|. (complement (upLeftMask b False source .|. upRightMask b False source .|. downLeftMask b False source .|. downRightMask b False source) .&. bishopTable source))
            ++ genMoves (BitBoard wpT wnT wbT wrT wqT wkT bpT bnT bbT brT restQueens bkT) 10

    genMoves (BitBoard _ _ _ _ _ _ _ _ _ _ _ bk) 11 = let (source, _) = popLSB bk in
            completeMoves 11 source (complement (getBlackPieces b) .&. kingTable source)

    genMoves _ _ = error "genMoves: invalid piece for black"

genBlackKingMoves :: ChessState -> [Move]
genBlackKingMoves (ChessState (BitBoard wpT wnT wbT wrT wqT wkT bpT bnT bbT brT bqT bkT) _ castles _ _ _ _)  =
    [(1 `unsafeShiftL` 24) .|. (11 `unsafeShiftL` 14) .|. (d `unsafeShiftL` 7) .|. 59| (c, f, tf, d) <- [(4, 0x0600000000000000, 0x0E00000000000000, 57), (8, 0x7000000000000000, 0x3800000000000000, 61)], castles .&. c /= 0, (allPieces .&. f) == 0, (enemyThreatens .&. tf) == 0]
    ++ genMoves b 11
    where
    enemyThreatens = foldl (\acc m -> acc .|. bit (word64ToInt $ getDestination m)) (0 :: Word64) $ genAllMoves (ChessState (BitBoard wpT wnT wbT wrT wqT wkT bpT bnT bbT brT bqT bkT) True castles 0 0 0 0) True False
    allPieces = getAllPieces b
    b = BitBoard wpT wnT wbT wrT wqT wkT bpT bnT bbT brT bqT bkT

    completeMoves :: Word64 -> Word64 -> Word64 -> [Move]
    completeMoves _ _ 0 = []
    completeMoves p s d = let (destination, rest) = popLSB d
                              capture = intToWord64 $ if (bit (word64ToInt destination) .&. allPieces) /= 0 then 1 else 0
                          in
                              ((capture `unsafeShiftL` 22) .|. ( p `unsafeShiftL` 14) .|. ( destination `unsafeShiftL` 7) .|.  s) : completeMoves p s rest

    genMoves (BitBoard _ _ _ _ _ _ _ _ _ _ _ bk) 11 = let (source, _) = popLSB bk in
            completeMoves 11 source (complement (getBlackPieces b) .&. kingTable source)

    genMoves _ _ = error "genMoves: invalid piece for black"

genLegalBlackKingMoves :: ChessState -> [Move]
genLegalBlackKingMoves (ChessState b _ castles ep hmc fmc zHash) =
    [move | move <- genBlackKingMoves (ChessState b False castles ep hmc fmc zHash), isLegalMove move]
    where
        isLegalMove :: Move -> Bool
        isLegalMove m = let (ChessState b' _ _ _ _ _ _) = applyMove (ChessState b False castles ep hmc fmc zHash) m in
            (getPieceBits b' 11 .&. foldl (\acc md -> acc .|. bit (word64ToInt $ getDestination md)) (0 :: Word64) (genAllMoves (ChessState b' True 0 0 0 0 0) False True)) == 0

genWhiteKingMoves :: ChessState -> [Move]
genWhiteKingMoves (ChessState (BitBoard wpT wnT wbT wrT wqT wkT bpT bnT bbT brT bqT bkT) _ castles _ _ _ _)  =
    [(1 `unsafeShiftL` 24) .|. (5 `unsafeShiftL` 14) .|. (d `unsafeShiftL` 7) .|. 3| (c, f, tf, d) <- [(1, 0x0000000000000006, 0x000000000000000E, 1), (2, 0x0000000000000070, 0x0000000000000038, 5)], castles .&. c /= 0, (allPieces .&. f) == 0, (enemyThreatens .&. tf) == 0]
    ++ genMoves b 5
    where
    enemyThreatens = foldl (\acc m -> acc .|. bit (word64ToInt $ getDestination m)) (0 :: Word64) $ genAllMoves (ChessState (BitBoard wpT wnT wbT wrT wqT wkT bpT bnT bbT brT bqT bkT) True castles 0 0 0 0) False True
    allPieces = getAllPieces b
    b = BitBoard wpT wnT wbT wrT wqT wkT bpT bnT bbT brT bqT bkT

    completeMoves :: Word64 -> Word64 -> Word64 -> [Move]
    completeMoves _ _ 0 = []
    completeMoves p s d = let (destination, rest) = popLSB d
                              capture = intToWord64 $ if (bit (word64ToInt destination) .&. allPieces) /= 0 then 1 else 0
                          in
                              ((capture `unsafeShiftL` 22) .|. ( p `unsafeShiftL` 14) .|. ( destination `unsafeShiftL` 7) .|.  s) : completeMoves p s rest

    genMoves (BitBoard _ _ _ _ _ _ _ _ _ _ _ bk) 5 = let (source, _) = popLSB bk in
            completeMoves 5 source (complement (getWhitePieces b) .&. kingTable source)

    genMoves _ _ = error "genMoves: invalid piece for White"

genLegalWhiteKingMoves :: ChessState -> [Move]
genLegalWhiteKingMoves (ChessState b _ castles ep hmc fmc zHash) =
    [move | move <- genWhiteKingMoves (ChessState b True castles ep hmc fmc zHash), isLegalMove move]
    where
        isLegalMove :: Move -> Bool
        isLegalMove m = let (ChessState b' _ _ _ _ _ _) = applyMove (ChessState b True castles ep hmc fmc zHash) m in
            (getPieceBits b' 5 .&. foldl (\acc md -> acc .|. bit (word64ToInt $ getDestination md)) (0 :: Word64) (genAllMoves (ChessState b' False 0 0 0 0 0) False True)) == 0

genAllLegalMoves :: ChessState -> [Move]
genAllLegalMoves (ChessState b True castles ep hmc fmc zHash) =
    [move | move <- genAllMoves (ChessState b True castles ep hmc fmc zHash) False False, isLegalMove move]
    where
        isLegalMove :: Move -> Bool
        isLegalMove m = let (ChessState b' _ _ _ _ _ _) = applyMove (ChessState b True castles ep hmc fmc zHash) m in
            (getPieceBits b' 5 .&. foldl (\acc md -> acc .|. bit (word64ToInt $ getDestination md)) (0 :: Word64) (genAllMoves (ChessState b' False 0 0 0 0 0) False True)) == 0
genAllLegalMoves (ChessState b False castles ep hmc fmc zHash) =
    [move | move <- genAllMoves (ChessState b False castles ep hmc fmc zHash) False False, isLegalMove move]
    where
        isLegalMove :: Move -> Bool
        isLegalMove m = let (ChessState b' _ _ _ _ _ _) = applyMove (ChessState b False castles ep hmc fmc zHash) m in
            (getPieceBits b' 11 .&. foldl (\acc md -> acc .|. bit (word64ToInt $ getDestination md)) (0 :: Word64) (genAllMoves (ChessState b' True 0 0 0 0 0) False True)) == 0

genAllCaptures :: ChessState -> [Move]
genAllCaptures (ChessState b True castles ep hmc fmc zHash) =
    [move | move <- genAllMoves (ChessState b True castles ep hmc fmc zHash) False True, isLegalMove move]
    where
        isLegalMove :: Move -> Bool
        isLegalMove m = let (ChessState b' _ _ _ _ _ _) = applyMove (ChessState b True castles ep hmc fmc zHash) m in
            (getPieceBits b' 5 .&. foldl (\acc md -> acc .|. bit (word64ToInt $ getDestination md)) (0 :: Word64) (genAllMoves (ChessState b' False 0 0 0 0 0) False True)) == 0

genAllCaptures (ChessState b False castles ep hmc fmc zHash) =
    [move | move <- genAllMoves (ChessState b False castles ep hmc fmc zHash) False True, isLegalMove move]
    where
        isLegalMove :: Move -> Bool
        isLegalMove m = let (ChessState b' _ _ _ _ _ _) = applyMove (ChessState b False castles ep hmc fmc zHash) m in
            (getPieceBits b' 11 .&. foldl (\acc md -> acc .|. bit (word64ToInt $ getDestination md)) (0 :: Word64) (genAllMoves (ChessState b' True 0 0 0 0 0) False True)) == 0

inCheck :: ChessState -> Bool
inCheck (ChessState b white _ _ _ _ _) = let
    pNum =  if white then 5 else 11 in
    (getPieceBits b pNum .&. foldl (\acc md -> acc .|. bit (word64ToInt $ getDestination md)) (0 :: Word64) (genAllMoves (ChessState b (not white) 0 0 0 0 0) False True)) /= 0