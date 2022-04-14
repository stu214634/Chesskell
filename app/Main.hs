module Main where

import ChessIO (parseFENBoard, showMove)
import Data.Char (digitToInt)
import qualified Data.HashTable.IO as H
import GameTree (GameTree (GameTree), alphaBetaWithMemory, gameTree, pvsWithMemory, gameTreeUsingTT)
import Model (Move, TT, ChessState)
import System.IO (BufferMode (LineBuffering), hSetBuffering, stdin, stdout)
import qualified Control.Monad

startingState :: ChessState
startingState = parseFENBoard "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1"

sAlpha :: Int
sAlpha = -0x0FFFFFFFFFFFFFFF
sBeta :: Int
sBeta = 0x0FFFFFFFFFFFFFFF

main :: IO ()
main = do
  hSetBuffering stdin LineBuffering
  hSetBuffering stdout LineBuffering
  tt <- H.newSized 100000000
  gameLoop tt

gameLoop :: TT -> IO ()
gameLoop tt = do
  input <- getLine
  let args = words input
  case head args of
    "position" -> waitForGo (gameTreeUsingTT tt $ parseFENBoard (unwords $ drop 2 args)) tt
    _ -> putStrLn "Unknown command"
  gameLoop tt


waitForGo :: GameTree -> TT -> IO ()
waitForGo (GameTree origState children) tt = do
  input2 <- getLine
  let args2 = words input2
  let depth = digitToInt $ head $ args2 !! 1
  case head args2 of
    "go" -> do
      iterDeep 1
      bestMove <- getBestMove
      putStrLn ("bestmove " ++ bestMove)
      where
        getBestMove :: IO String
        getBestMove = do
          (bestMove, _, state) <- foldl foldFunc (return (0, return sAlpha, startingState)) children
          occCount <- H.lookup tt state
          case occCount of
            Just (hash, depth, f, v, c) -> putStrLn ("I've seen this position (" ++ show hash ++ ") " ++ show c ++ " times") >> H.insert tt state (hash, depth, f, v, c+1)
            Nothing -> putStrLn "Cache miss after search?"
          return (showMove bestMove)

        foldFunc :: IO (Move, IO Int, ChessState) -> (Move, GameTree) -> IO (Move, IO Int, ChessState)
        foldFunc ct (m, GameTree state ch) = do
            (cml, csu, css) <- ct
            csl <- csu
            nScore <- pvsWithMemory tt (GameTree state ch) depth (-sBeta) (-csl)
            putStrLn $ showMove m ++ ": " ++ show nScore
            if (-nScore) > csl then
              return (m, return (-nScore), state)
            else
              return (cml, return csl, css)

        iterDeep n = do
          _ <- pvsWithMemory tt (GameTree origState children) n sAlpha sBeta
          Control.Monad.when (n < (depth - 1)) $ iterDeep (n+1)


    _ -> putStrLn "Expected go"

--