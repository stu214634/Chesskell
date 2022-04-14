module ChessIO where
import Model ( ChessState (ChessState), BitBoard(..), getSource, getDestination, getPromotion, parsePiece, showPiece, showPos )
import Data.Word (Word64, Word64, Word64)
import Data.Bits ( Bits((.|.), unsafeShiftL, xor, bit, (.&.)) )
import Data.Char ( ord, digitToInt, toLower )
import BitFuncs ( intToWord64, pieceAt )
import Zobrist (random64, zBlack, zCastle, zEnPassant)
import Data.Vector ((!))
import Data.List ( foldl1', foldl' )
import MoveApplication (getAllPieces)

-- | Split a string into a list of strings, separated by a forward slash
splitAtSlash :: String -> [String]
splitAtSlash [] = []
splitAtSlash s =
    let (first, rest) = break (== '/') s
    in first : splitAtSlash (drop 1 rest)

parseBoard :: String -> BitBoard
parseBoard str = BitBoard {
    whitePawns = parseFENPiece 'P' str,
    whiteKnights = parseFENPiece 'N' str,
    whiteBishops = parseFENPiece 'B' str,
    whiteRooks = parseFENPiece 'R' str,
    whiteQueens = parseFENPiece 'Q' str,
    whiteKing = parseFENPiece 'K' str,
    blackPawns = parseFENPiece 'p' str,
    blackKnights = parseFENPiece 'n' str,
    blackBishops = parseFENPiece 'b' str,
    blackRooks = parseFENPiece 'r' str,
    blackQueens = parseFENPiece 'q' str,
    blackKing = parseFENPiece 'k' str
}
    where
        parseFENPiece :: Char -> String -> Word64
        parseFENPiece c pieceString = foldl (\acc x -> unsafeShiftL acc (if x `elem` ['1'..'8'] then digitToInt x else 1) .|. (if x == c then 1 else 0)) 0 pieceString

-- | Parses a FEN string into a ChessState
parseFENBoard :: String -> ChessState
parseFENBoard fen =
    let [boardStr, turnStr, castlingStr, enPassantStr, halfMoveClockStr, fullMoveNumberStr] = words fen
        board = parseBoard $ filter (/='/') boardStr
        turn = turnStr == "w"
        castling = parseCastling castlingStr
        enPassant = parseEnPassant enPassantStr
        halfMoveClock = read halfMoveClockStr
        fullMoveNumber = read fullMoveNumberStr
        zhash = zobristHash board `xor` (if turn then zBlack else 0) `xor` (if enPassant /= 0 then zEnPassant enPassant else 0) `xor`
         (if castlingStr == "-" then 0 else foldl' (\acc x -> case x of 'K' -> acc `xor` zCastle 0; 'Q' -> acc `xor` zCastle 1; 'k' -> acc `xor` zCastle 2; 'q' -> acc `xor` zCastle 3; _ -> acc) 0 castlingStr)
    in ChessState board turn castling enPassant halfMoveClock fullMoveNumber zhash

    where
        parseCastling :: String -> Word64
        parseCastling str = if str == "-" then 0 else foldl (\acc x -> case x of 'K' -> acc .|. 1; 'Q' -> acc .|. 2; 'k' -> acc .|. 4; 'q' -> acc .|. 8; _ -> acc) 0 str
        parseEnPassant :: String -> Word64
        parseEnPassant str = if str == "-" then 0 else intToWord64 $ (digitToInt (last str) - 1) * 8 + (7 - (ord (head str) - ord 'a'))
        zobristHash :: BitBoard ->  Word64
        zobristHash board  =
            foldl1' xor (map zobristHashBoard [0..63])
            where
            allPieces = getAllPieces board
            zobristHashBoard :: Int -> Word64
            zobristHashBoard idx = case bit idx .&. allPieces of
                0 -> 0
                _ -> random64 ! ((pieceAt board idx * 64) + idx)


-- | Parse a String to a Move
parseMove :: String -> Word64
parseMove str =
    let
        piece = parsePiece $ head str
        capture = intToWord64 $ if str !! 3 == 'x' then 1 else 0
        enPassant = intToWord64 $ if last str == 'e' then 1 else 0
        from = intToWord64 $ (digitToInt (str !! 2) - 1) * 8 + (7 - (ord (str !! 1) - ord 'a'))
        to = intToWord64 $ (digitToInt (str !! (if capture == 1 then 5 else 4)) - 1) * 8 + (7 - (ord (str !! (if capture == 1 then 4 else 3)) - ord 'a'))
        promotion = if last str `elem` "QRBNqrbn" then parsePiece (last str) else 0
        doublePawnPush = intToWord64 $ if (piece == 0 || piece == 6) && ((from - to) == 16 || (to - from) == 16) then 1 else 0
        castling = intToWord64 $ if (piece == 5 || piece == 11) && ((from - to) == 2 || (to - from) == 2) then 1 else 0
    in
        ((((((doublePawnPush `unsafeShiftL` 1 .|. castling) `unsafeShiftL` 1 .|. enPassant) `unsafeShiftL` 1 .|. capture) `unsafeShiftL` 4 .|. promotion) `unsafeShiftL` 4 .|. piece) `unsafeShiftL` 7 .|. to) `unsafeShiftL` 7 .|. from

-- | Decodes a Move to a String
showMove :: Word64 -> String
showMove move =
    let
        from = showPos (getSource move)
        to = showPos (getDestination move)
        promotion = if getPromotion move /= 0 then [showPiece (getPromotion move)] else ""
    in
        from ++ to ++ map toLower promotion


