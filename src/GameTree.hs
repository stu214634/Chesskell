{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
--
module GameTree where
import Model (ChessState (ChessState, white, board, zobristHash), Move, getDestination, TT, getPiece)
import GHC.Generics (Generic)
import Control.Parallel.Strategies (NFData, parMap, rdeepseq)
import qualified Data.Bifunctor
import MoveGeneration (genAllLegalMoves, inCheck, genAllMoves, genAllCaptures)
import MoveApplication (applyMove, getPieceBits, getBlackPieces, getWhitePieces)
import Data.Word (Word64)
import Data.Bits (Bits(popCount, (.&.), unsafeShiftL, (.|.), bit), FiniteBits (countTrailingZeros))
import BitMasks (bottomRowMask, kingTable)
import BitFuncs (word64ToInt, intToWord64, pieceAt)
import qualified Data.HashTable.IO as H
import Data.List (sortBy, sortOn)
import GHC.IO (unsafeDupablePerformIO)


pToVal :: Word64 -> Int
pToVal 0 = 100
pToVal 1 = 300
pToVal 2 = 300
pToVal 3 = 500
pToVal 4 = 900
pToVal 5 = 20000
pToVal 6 = -100
pToVal 7 = -300
pToVal 8 = -300
pToVal 9 = -500
pToVal 10 = -900
pToVal 11 = -20000

pPosWhiteScore :: Word64 -> Int
pPosWhiteScore 1 = 0
pPosWhiteScore 2 = 10
pPosWhiteScore 3 = 20
pPosWhiteScore 4 = 30
pPosWhiteScore 5 = 40
pPosWhiteScore 6 = 50

pPosBlackScore :: Word64 -> Int
pPosBlackScore 1 = 50
pPosBlackScore 2 = 40
pPosBlackScore 3 = 30
pPosBlackScore 4 = 20
pPosBlackScore 5 = 10
pPosBlackScore 6 = 0

-- + pWorth
--        - (whiteKingThreatLevel * 20) + (blackKingThreatLevel * 20) + checkScore + whiteFianchetto + blackFianchetto + whiteKnightP + blackKnightP +
pRowMask :: Word64 -> Word64
pRowMask n = bottomRowMask `unsafeShiftL` (word64ToInt n*8)

score :: ChessState -> Int
score (ChessState bitboard isWhite _ _ hm _ _)
    | hm >= 100 = 0
    | otherwise = (if isWhite then 1 else (-1)) * (matScore + (popCount attackMapWhite * 5)
        - (popCount attackMapBlack * 5) + (popCount defendMapWhite * 10) - (popCount defendMapBlack * 10) - (whiteKingThreatLevel * 20) + (blackKingThreatLevel * 20))

    where
        wk = getPieceBits bitboard 5
        bk = getPieceBits bitboard 11
        --wb = getPieceBits bitboard 2
        --bb = getPieceBits bitboard 8
        --wp = getPieceBits bitboard 0
        --bp = getPieceBits bitboard 6
        --wn = getPieceBits bitboard 1
        --bn = getPieceBits bitboard 7
        wkP = intToWord64 $ countTrailingZeros wk
        bkP = intToWord64 $ countTrailingZeros bk
        blackPieces = getBlackPieces bitboard
        whitePieces = getWhitePieces bitboard
        --whiteKnightP = popCount (wn .&. whiteKnightPunishment) * (-30)
        --blackKnightP = popCount (bn .&. blackKnightPunishment) * 30
        threatMapWhite = foldl (\acc m -> acc .|. bit (word64ToInt $ getDestination m)) (0 :: Word64) $ genAllMoves (ChessState bitboard True 0 0 0 0 0) True False
        attackMapWhite = threatMapWhite .&. blackPieces
        defendMapBlack = threatMapBlack .&. blackPieces
        threatMapBlack = foldl (\acc m -> acc .|. bit (word64ToInt $ getDestination m)) (0 :: Word64) $ genAllMoves (ChessState bitboard False 0 0 0 0 0) True False
        attackMapBlack = threatMapBlack .&. whitePieces
        defendMapWhite = threatMapWhite .&. whitePieces
        whiteKingThreatLevel =  popCount (threatMapBlack .&. kingTable wkP)
        blackKingThreatLevel =  popCount (threatMapWhite .&. kingTable bkP)
        --checkScore = whiteInCheck + blackInCheck
        --whiteInCheck = if threatMapBlack .&. wk == 0 then 0 else -50
        --blackInCheck = if threatMapWhite .&. bk == 0 then 0 else 50
        --whiteFianchetto = (if whiteWBishopFianchettoSpot .&. wb /= 0 then 5 else 0) * (popCount (whiteWPawnsForFianchetto .&. wp) + 1) * (if wkP <= 1 then 2 else 1)
        --                + (if whiteBBishopFianchettoSpot .&. wb /= 0 then 5 else 0) * (popCount (whiteBPawnsForFianchetto .&. wp) + 1) * (if wkP <= 7 && wkP >= 5 then 2 else 1)
        --blackFianchetto = -((if blackWBishopFianchettoSpot .&. bb /= 0 then 5 else 0) * (popCount (blackWPawnsForFianchetto .&. bp) + 1) * (if bkP >= 56 && bkP <= 57 then 2 else 1)
        --                + (if blackBBishopFianchettoSpot .&. bb /= 0 then 5 else 0) * (popCount (blackBPawnsForFianchetto .&. bp) + 1) * (if bkP >= 61 then 2 else 1))
        --pWorth :: Int
        --pWorth = sum [pPosWhiteScore i * popCount (getPieceBits bitboard 0 .&. pRowMask i) - pPosBlackScore i * popCount (getPieceBits bitboard 6 .&. pRowMask i)| i <- [1..6]]
        matScore = sum [pToVal p * popCount (getPieceBits bitboard p) | p <- [0..11]]

data GameTree = GameTree !ChessState ![(Move, GameTree)]
    deriving (Show, Generic, NFData)

gameTree :: ChessState -> GameTree
gameTree state = case genAllLegalMoves state of
    [] -> GameTree state []
    ms -> GameTree state $ map (Data.Bifunctor.second gameTree) (sortOn (score . snd) (map (\m -> (m, applyMove state m)) ms))


captureTree :: ChessState -> GameTree
captureTree state = case genAllCaptures state of
    [] -> GameTree state []
    ms -> GameTree state (map (Data.Bifunctor.second captureTree . (\m -> (m, applyMove state m))) (sortBy compareCapture ms))
    where
        compareCapture :: Move -> Move -> Ordering
        m1 `compareCapture` m2 =
            let isWhite = white state
                capturer1 = word64ToInt $ getPiece m1 - (if isWhite then 0 else 5)
                captured1 = pieceAt (board state) (word64ToInt $ getDestination m1) - (if isWhite then 0 else 5)
                capturer2 = word64ToInt $ getPiece m2 - (if isWhite then 0 else 5)
                captured2 = pieceAt (board state) (word64ToInt $ getDestination m2) - (if isWhite then 0 else 5) in
                (capturer1 - captured1) `compare` (capturer2 - captured2)


gameTreeUsingTT :: TT -> ChessState -> GameTree
gameTreeUsingTT tt state = case genAllLegalMoves state of
    [] -> GameTree state []
    ms -> GameTree state $ map (Data.Bifunctor.second (gameTreeUsingTT tt)) (sortOn (ttOrScore . snd) (map (\m -> (m, applyMove state m)) ms))
    where
        ttOrScore :: ChessState -> Int
        ttOrScore s = do
            let entry = unsafeDupablePerformIO (H.lookup tt s)
            case entry of
                Just (_, _, f, v, _) -> case f of
                    0 -> v + 100
                    1 -> v
                    2 -> v + 10
                Nothing -> score s

-- | Perft functions
nodes :: GameTree -> Int -> Int
nodes _ 0 = 1
nodes (GameTree _ c) n = sum $ parMap rdeepseq (\(_, gT) -> nodes gT (n-1)) c

fLevel :: GameTree -> Int -> [(Move, Int)]
fLevel (GameTree _ c) n = map (\(m, gT) -> (m, nodes gT (n-1))) c

pvsWithMemory :: TT -> GameTree -> Int -> Int -> Int -> IO Int
pvsWithMemory _ (GameTree state _) 0 alpha beta = return $ quiessence (captureTree state) alpha beta
pvsWithMemory _ (GameTree state []) n _ _  = return $ if inCheck state then -9999999 - n else 0
pvsWithMemory tt (GameTree state children) n alpha beta = do
    entry <- H.lookup tt state
    case entry of
        Just (hash, depth, f, v, c) -> if hash /= fromIntegral (zobristHash state) then handleContinue alpha beta 0 0 else if c >= 2 then return 0 else if depth >= n then handleReturn else handleContinue alpha beta v c
            where
                handleReturn
                        | f == 1 = return v
                        | f == 0 = handleContinue (max alpha v) beta v c
                        | otherwise = handleContinue alpha (min beta v) v c
        Nothing -> handleContinue alpha beta 0 0
    where
        handleContinue a b v c =
            if a >= b then return v
            else do
            g <- pvs tt (GameTree state children) n a b
            if g <= alpha then
                 H.insert tt state (fromIntegral $ zobristHash state, n, 2, g, c)
            else if g >= b then
                H.insert tt state (fromIntegral $ zobristHash state, n, 0, g, c)
            else
                H.insert tt state (fromIntegral $ zobristHash state, n, 1, g, c)
            return g


pvs :: TT -> GameTree -> Int -> Int -> Int -> IO Int
pvs _ (GameTree state _) 0 alpha beta = return $ quiessence (captureTree state) alpha beta
pvs _ (GameTree state []) n _ _ = return $ if inCheck state then -9999999 - n else 0
pvs tt (GameTree _ children) n alpha beta = ev True n children alpha beta
    where
        ev :: Bool -> Int -> [(Move, GameTree)] -> Int -> Int -> IO Int
        ev True depth ((_, gt):xs) al be = do
            search <- pvsWithMemory tt gt (depth-1) (-be) (-al)
            let eval = -search
            let nAlpha = max al eval
            if nAlpha >= beta then return nAlpha else ev False depth xs nAlpha beta
        ev False _ [] al _ = return al
        ev False depth ((_, gt): xs) al be = do
            search <- pvsWithMemory tt gt (depth-1) (-al - 1) (-al)
            let eval = -search
            fSearch <- if al < eval && eval < be then pvs tt gt (depth-1) (-be) (-eval) else return (-eval)
            let fEval = -fSearch
            let nAlpha = max al fEval
            if nAlpha >= beta then return nAlpha else ev False depth xs nAlpha beta


alphaBetaWithMemory :: TT -> GameTree -> Int -> Int -> Int -> IO Int
alphaBetaWithMemory _ (GameTree state _) 0 alpha beta = return $ quiessence (captureTree state) alpha beta
alphaBetaWithMemory _ (GameTree state []) n _ _  = return $ if inCheck state then -9999999 - n else 0
alphaBetaWithMemory tt (GameTree state children) n alpha beta = do
    entry <- H.lookup tt state
    case entry of
        Just (hash, depth, f, v, c) -> if hash /= fromIntegral (zobristHash state) then handleContinue alpha beta 0 0 else if c >= 2 then return 0 else if depth >= n then handleReturn else handleContinue alpha beta v c
            where
                handleReturn
                        | f == 1 = putStrLn "Exact cache hit" >> return v
                        | f == 0 = handleContinue (max alpha v) beta v c
                        | otherwise = handleContinue alpha (min beta v) v c
        Nothing -> handleContinue alpha beta 0 0
    where
        handleContinue a b v c =
            if a >= b then return v
            else do
            g <- alphaBeta tt (GameTree state children) n a b
            if g <= alpha then
                 H.insert tt state (fromIntegral $ zobristHash state, n, 2, g, c)
            else if g >= b then
                H.insert tt state (fromIntegral $ zobristHash state, n, 0, g, c)
            else
                H.insert tt state (fromIntegral $ zobristHash state, n, 1, g, c)
            return g

alphaBeta :: TT -> GameTree -> Int -> Int -> Int -> IO Int
alphaBeta tt (GameTree _ children) n alpha beta = ev children (-1000000) alpha
    where
        ev :: [(Move, GameTree)] -> Int -> Int -> IO Int
        ev [] maxEval _ = return maxEval
        ev ((_, gT):xs) maxEval al = do
            eval <- alphaBetaWithMemory tt gT (n-1) (-beta) (-al)
            let val = -eval
            let nMaxEval = max val maxEval
            let nAlpha = max al val
            if beta <= nAlpha then return nMaxEval else ev xs nMaxEval nAlpha

-- | Quiessence search
quiessence :: GameTree -> Int -> Int -> Int
quiessence (GameTree state [])  _ _  = score state
quiessence (GameTree state children) alpha beta = ev children alpha
    where
        ev :: [(Move, GameTree)] -> Int -> Int
        ev [] al = al
        ev ((_, gT):xs) al = do
            let standPat = score state
            if standPat >= beta then beta
            else if standPat + 5000 < alpha then alpha
            else do
                let mAlpha = max al standPat
                let eval = quiessence gT (-beta) (-mAlpha)
                let val = -eval
                let nAlpha = max mAlpha val
                if beta <= val then beta else ev xs nAlpha

