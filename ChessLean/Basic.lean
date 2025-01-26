inductive Piece where
  | king : Piece
  | queen : Piece
  | rook : Piece
  | bishop : Piece
  | knight : Piece
  | pawn : Piece
  | empty : Piece
deriving Inhabited, DecidableEq, BEq, Hashable

def Piece.toChar : Piece → Char
  | Piece.king => 'K'
  | Piece.queen => 'Q'
  | Piece.rook => 'R'
  | Piece.bishop => 'B'
  | Piece.knight => 'N'
  | Piece.pawn => 'P'
  | Piece.empty => ' '


instance : ToString Piece where
  toString p := toString (Piece.toChar p)

def Board := Array (Array Piece)

def Board.empty : Board := Array.mkArray 8 (Array.mkArray 8 Piece.empty)

def row1 : Array Piece := #[Piece.rook, Piece.knight, Piece.bishop, Piece.queen, Piece.king, Piece.bishop, Piece.knight, Piece.rook]

def row2 : Array Piece := #[Piece.pawn, Piece.pawn, Piece.pawn, Piece.pawn, Piece.pawn, Piece.pawn, Piece.pawn, Piece.pawn]

def b : Board := #[row1, row2]

#eval b

#eval Array.map (λ row => (Array.map (λ p => Piece.toChar p) row)) b

-- def Board.toString (b : Board) : List List Char :=
  -- Array.map (λ row => (Array.map (λ p => Piece.toChar p) row))


instance : ToString Board where
  toString b := "Board100"


#eval Board.empty

def hello := "world"
