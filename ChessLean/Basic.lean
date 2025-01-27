inductive Color where
  | white : Color
  | black : Color


inductive Piece where
  | king : Piece
  | queen : Piece
  | rook : Piece
  | bishop : Piece
  | knight : Piece
  | pawn : Piece
deriving Inhabited, DecidableEq, BEq, Hashable, Repr


inductive Move where
  | up : Move
  | right : Move
  | diagR : Move
  | diagL : Move

def Piece.toChar : Piece → Char
  | Piece.king => 'K'
  | Piece.queen => 'Q'
  | Piece.rook => 'R'
  | Piece.bishop => 'B'
  | Piece.knight => 'N'
  | Piece.pawn => 'P'


def Piece.toString (p : Piece) : String :=
  p.toChar.toString


instance : ToString Piece where
  toString p := p.toString


structure ColoredPiece where
  color : Color
  piece : Piece


def Square := Option Piece

instance : Inhabited Square where
  default := none


def Square.toString (s : Square) : String :=
  match s with
  -- | none => "⬝"
  | none => "⬝"
  | some p => p.toString


instance : ToString Square where
  toString s := s.toString


abbrev Board := List (List Square)


abbrev Position := (Nat, Nat)


def Board.empty : Board := List.replicate 8 (List.replicate 8 none)


def r : List Square := [some Piece.rook, some Piece.knight, some Piece.bishop, some Piece.queen,
                        some Piece.king, some Piece.bishop, some Piece.knight, some Piece.rook]
def ps : List Square := [some Piece.pawn, some Piece.pawn, some Piece.pawn, some Piece.pawn, some Piece.pawn,
                         some Piece.pawn, some Piece.pawn, some Piece.pawn]
def blank : List Square := List.replicate 8 none
def b : Board := [r, ps, blank, blank, blank, blank, ps, r]

def Board.starting : Board := b


def join (xs : List String) (s : String) : String :=
  (xs.foldl (λ acc x => acc ++ x ++ s) "").dropRight s.length


def mtx2string (xss : List (List String)) : String :=
  join (List.map (λ xs => join xs " ") xss) "\n"


-- TODO: Why does this not work on #eval?
def Board.toString (b : Board) : String :=
  mtx2string (List.map (λ row => List.map (λ p => p.toString) row) b)


-- TODO: make this nontrivial
def Board.valid (b : Board) (idx : Nat × Nat) : Prop :=
  sorry


-- TODO: implement this, and get notation for it

instance : GetElem Board Nat (List Square) (λ b idx => True) where
  getElem board i h := board.get! i


instance : GetElem Board (Nat × Nat) Square (λ b idx => True) where
  getElem board pos h :=
    let (i, j) := pos
    let row := List.get! board i
    List.get! row j


instance : ToString Board where
  toString b := Board.toString b


-- instance : GetElem Board (Nat × Nat) Square ()
--   getElem b (i j) := (b.get! ij.fst).get! ij.snd


#eval List.range 8


-- moves 1 1 1 1 1 1 1 1 = [(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1)]
-- moves


def moveH (n : Nat) : List (Int × Int) :=
  List.flatten [List.range (n + 1) |>.tail |>.map (λ i => (0, Int.ofNat i)), List.range (n + 1) |>.tail |>.map (λ i => (0, -Int.ofNat i))]

def moveV (n : Nat) : List (Int × Int) :=
  List.flatten [List.range (n + 1) |>.tail |>.map (λ i => (Int.ofNat i, 0)), List.range (n + 1) |>.tail |>.map (λ i => (-Int.ofNat i, 0))]

def moveD (n : Nat) : List (Int × Int) :=
  List.flatten [List.range (n + 1) |>.tail |>.map (λ i => (Int.ofNat i, Int.ofNat i)), List.range (n + 1) |>.tail |>.map (λ i => (-Int.ofNat i, -Int.ofNat i)),
                List.range (n + 1) |>.tail |>.map (λ i => (-Int.ofNat i, Int.ofNat i)), List.range (n + 1) |>.tail |>.map (λ i => (Int.ofNat i, -Int.ofNat i))]

#eval moveD 3

def deltas (h v d : Nat) : List (Int × Int) :=
  List.flatten [moveH h, moveV v, moveD d]


def Piece.delta : Piece -> List (Int × Int)
  | Piece.king => deltas 1 1 1
  | Piece.queen => deltas 8 8 8
  | Piece.rook => deltas 8 8 0
  | Piece.bishop => deltas 0 0 8
  | Piece.knight => [(-2, -1), (-2, 1), (-1, -2), (-1, 2), (1, -2), (1, 2), (2, -1), (2, 1)] -- TODO: check
  | Piece.pawn => [(2, 0), (1, 0)] -- TODO: add black/white


#eval Piece.bishop.delta


def inBoard? (i j : Int) : Bool :=
  i >= 0 && i < 8 && j >= 0 && j < 8


def Piece.moves (p : Piece) (i j : Nat) : List (Nat × Nat) :=
  -- let valid? (di dj : Int) (i j : Nat) : Bool :=
    -- inBoard? (i + di) (j + dj) &&
  p.delta.map (λ (di, dj) => ((Int.ofNat i) + di, (Int.ofNat j) + dj)) |> List.filter (λ (i, j) => inBoard? i j) |> List.map (λ (i, j) => (i.toNat, j.toNat))


#eval Piece.moves Piece.knight 0 0


def Board.piece? (b : Board) (i j : Nat) : Bool :=
  match b[i][j]! with
  | none => false
  | _ => true


def validH? (b : Board) (i j : Nat) (di : Nat) : Bool :=
  sorry


#eval List.range' (5 + 1) 3 |>.map (λ i => (5, i))


def abs (x : Int) : Int :=
  if x > 0 then x else (-x)


partial def posV (i j : Int) (dj : Int) : List (Nat × Nat) :=
  if dj >= 0 then
    List.range' (j + 1).toNat dj.toNat |>.map (λ j' => (i.toNat, j'))
  else if j + dj >= 0 then
    posV i (j + dj - 1) (-dj)
  else
    []


#eval posV 5 5 (-1)


def posH (i j : Int) (di : Int) : List (Nat × Nat) :=
  posV j i di |>.map (λ (j, i) => (i, j))


def inc (x : Int) : Int :=
  x + 1


def dec (x : Int) : Int :=
  x - 1


def neg? (x : Int) : Bool :=
  x < 0

def pos? (x : Int) : Bool :=
  x > 0

def Nat.pos? (x : Nat) : Bool :=
  x > 0

-- TODO: extend to all types
def complement (f : Int -> Bool) : Int -> Bool :=
  λ x => !f x


partial def parseIdx (i : Int) (di : Int) : Option (Nat × Nat) :=
  if List.all [i, di] (complement neg?) then
    match List.map Int.toNat [i, di] with
    | [i, di] => some (i, di)
    | _ => none
  else if neg? di then
    parseIdx (i + di) (-di)
  else
    none


partial def parsePos (i j : Int) (di dj : Int) : Option ((Nat × Nat) × (Nat × Nat)) :=
  match parseIdx i di, parseIdx j dj with
  | some (i, di), some (j, dj) => some ((i, j), (di, dj))
  | _, _ => none


#eval (parsePos 1 2 3 4)

-- bottom right
partial def diagR (i j : Nat) (d : Nat) : List (Nat × Nat) :=
  List.zip (List.range' i (d + 1)) (List.range' j (d + 1))


-- bottom left
partial def diagL (i j : Nat) (d : Nat) : List (Nat × Nat) :=
  List.zip (List.range' i (d + 1)) (List.range' (j - d) (d + 1)).reverse


partial def right (i j : Nat) (d : Nat) : List (Nat × Nat) :=
  List.range' j (d + 1) |>.map (λ j' => (i, j'))


-- TODO: strengthen precondition
partial def up (i j : Nat) (d : Nat) : List (Nat × Nat) :=
  List.map Prod.swap (right j (i - d) d)


-- expect itop < ibot
def btwnUp  (ibot jleft : Nat) (itop jright : Nat) : List (Nat × Nat) :=
  up ibot jleft (ibot - itop) |>.filter (λ (i, j) => (i, j) ≠ (ibot, jleft) && (i, j) ≠ (itop, jright))


-- expect jleft < jright
def btwnRight (ibot jleft : Nat) (itop jright : Nat) : List (Nat × Nat) :=
  right jleft ibot (jright - jleft) |>.filter (λ (i, j) => (i, j) ≠ (ibot, jleft) && (i, j) ≠ (itop, jright))


def btwnDiagR (itop jleft : Nat) (ibot jright : Nat) : List (Nat × Nat) :=
  diagR itop jleft (ibot - itop) |>.filter (λ (i, j) => (i, j) ≠ (itop, jleft) && (i, j) ≠ (ibot, jright))


def btwnDiagL (itop jright : Nat) (ibot jleft : Nat) : List (Nat × Nat) :=
  diagL itop jright (ibot - itop) |>.filter (λ (i, j) => (i, j) ≠ (itop, jright) && (i, j) ≠ (ibot, jleft))


def up? (b : Board) (ibot jleft : Nat) (itop jright : Nat) : Bool :=
  if ibot < itop then
    up? b itop jright ibot jleft
  else
    let btwn := btwnUp ibot jleft itop jright
    btwn.all (λ (i, j) => !b.piece? i j)


def right? (b : Board) (ibot jleft : Nat) (itop jright : Nat) : Bool :=
  if jright < jleft then
    right? b itop jright ibot jleft
  else
    let btwn := btwnRight ibot jleft itop jright
    btwn.all (λ (i, j) => !b.piece? i j)


def diagR? (b : Board) (itop jleft : Nat) (ibot jright : Nat) : Bool :=
  if ibot < itop then
    diagR? b ibot jright itop jleft
  else
    let btwn := btwnDiagR itop jleft ibot jright
    btwn.all (λ (i, j) => !b.piece? i j)


def diagL? (b : Board) (itop jright : Nat) (ibot jleft : Nat) : Bool :=
  if jright < jleft then
    diagL? b ibot jleft itop jright
  else
    let btwn := btwnDiagL itop jright ibot jleft
    btwn.all (λ (i, j) => !b.piece? i j)


def btest : Board := [r,
                      ps,
                      blank,
                      [none, none, none, some Piece.king, none, none, none, none],
                      blank,
                      blank,
                      ps,
                      r]


def filterPieces (b : Board) (xs : List (Nat × Nat)) : List (Nat × Nat) :=
  xs.filter (λ (i, j) => !b.piece? i j)


def filterBlockingVertical (b : Board) (i j : Nat) (xs : List (Nat × Nat)) : List (Nat × Nat) :=
  xs.filter (λ (i', j') => up? b i j i' j')


def filterBlockingHorizontal (b : Board) (i j : Nat) (xs : List (Nat × Nat)) : List (Nat × Nat) :=
  xs.filter (λ (i', j') => right? b i j i' j')


def filterBlockingDiagonal (b : Board) (i j : Nat) (xs : List (Nat × Nat)) : List (Nat × Nat) :=
  xs.filter (λ (i', j') => diagR? b i j i' j')


-- TODO: test
-- TODO: need to add diagonal checks
def Board.moves (b : Board) (i j : Nat) : List (Nat × Nat) :=
  match b[i][j]! with
  | none => []
  | some p =>
    let ms := p.moves i j
    match p with
    | Piece.king => ms
    | Piece.queen => ms |> filterBlockingVertical b i j |> filterBlockingHorizontal b i j |> filterBlockingDiagonal b i j
    | Piece.rook => ms |> filterBlockingVertical b i j |> filterBlockingHorizontal b i j
    | Piece.bishop => ms |> filterBlockingDiagonal b i j
    | Piece.knight => ms
    | Piece.pawn => ms -- TODO: add black/white


partial def Board.set_row (b : Board) (i : Nat) (row : List Square) : Board :=
  b.set i row

def Board.set (b : Board) (i j : Nat) (s : Square) : Board :=
  let row := (b.get! i).set j s
  b.set_row i row


-- TODO: add features
def Board.show (b : Board) : IO Unit :=
  IO.println (Board.toString b)


#eval btest.show

#eval up? btest 3 3 1 3

#eval right? btest 4 0 4 8

#eval diagL? btest 1 5 3 3

#eval diagR? btest 1 1 4 4



def Board.move (b : Board) (x1 y1 : Nat) (x2 y2 : Nat) : Board :=
  (b.set x2 y2 b[x1][y1]!).set x1 y1 none


def Char.parseNat (c : Char) : Nat :=
  (c.toNat - '0'.toNat)


def parseMove (s : List Char) : Nat × Nat :=
  ((s.get! 0).parseNat, (s.get! 2).parseNat)


partial def loop (b : Board) : IO Unit := do
  let stdin ← IO.getStdin

  b.show

  IO.print "Piece to move: "
  let input ← stdin.getLine
  let (i, j) := parseMove input.trim.toList
  match b.moves i j with
  | [] => do
    IO.println "> No moves available. Please try again."
    loop b
  | ms => do
    IO.println s!"> Available moves: {ms}"

  IO.print "Move to: "
  let input ← stdin.getLine
  let (i', j') := parseMove input.trim.toList

  -- let b' := b.move i j i' j'
  loop (b.move i j i' j')


def play : IO Unit := do
  loop Board.starting


def hello := "world"
