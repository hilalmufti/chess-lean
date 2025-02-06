inductive Color where
  | white : Color
  | black : Color


def Color.toString : Color -> String
  | Color.white => "white"
  | Color.black => "black"

instance : ToString Color where
  toString c := c.toString


inductive Piece where
  | king : Piece
  | queen : Piece
  | rook : Piece
  | bishop : Piece
  | knight : Piece
  | pawn : Piece


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


abbrev ColorPiece := Color × Piece


#eval (Color.white, Piece.king)


def Square := Option ColorPiece

instance : Inhabited Square where
  default := none


def Square.toString (s : Square) : String :=
  match s with
  -- | none => "⬝"
  | none => "."
  | some (c, p) => p.toString



instance : ToString Square where
  toString s := s.toString


abbrev Board := List (List Square)


abbrev Position := (Nat, Nat)


def Board.empty : Board := List.replicate 8 (List.replicate 8 none)

def r : List Piece := [Piece.rook, Piece.knight, Piece.bishop, Piece.queen, Piece.king,
                       Piece.bishop, Piece.knight, Piece.rook]


def make_row (xs : List Piece) (c : Color) : List Square :=
  let rec go (xs : List Piece) (acc : List Square) : List Square :=
    match xs with
    | [] => acc
    | x :: xs => go xs ((some (c, x)) :: acc)
  go xs []

def r_white := make_row r Color.white
def r_black := make_row r Color.black

def pawns : List Piece := List.replicate 8 Piece.pawn
def ps_white := make_row pawns Color.white
def ps_black := make_row pawns Color.black

def blank : List Square := List.replicate 8 none
def b : Board := [r_black, ps_black, blank, blank, blank, blank, ps_white, r_white]


def Board.starting : Board := b


def String.join' (xs : List String) (s : String) : String :=
  let rec go (xs : List String) (acc : String) : String :=
    match xs with
    | [] => acc
    | x :: [] => acc ++ x
    | x :: xs => go xs (acc ++ x ++ s)
  go xs ""


def assocs_toString (xss : List (List String)) : String :=
  let rec go (xss : List (List String)) (acc : List String) : List String :=
    match xss with
    | [] => List.reverse acc
    | xs :: xss => go xss ((" ".join' xs) :: acc)

  "\n".join' (go xss [])


-- TODO: Why does this not work on #eval?
def Board.toString (b : Board) : String :=
  assocs_toString (List.map (List.map Square.toString) b)


-- TODO: make this nontrivial
def Board.valid (b : Board) (idx : Nat × Nat) : Prop :=
  sorry


instance : GetElem Board Nat (List Square) (λ b idx => True) where
  getElem board i h := board.get! i


instance : GetElem Board (Nat × Nat) Square (λ b idx => True) where
  getElem board pos h :=
    let (i, j) := pos
    List.get! (List.get! board i) j


instance : ToString Board where
  toString b := Board.toString b


def List.fsts {α β : Type} : List (α × β) -> List α
  | [] => []
  | (a, _) :: xs => a :: List.fsts xs


def List.snds {α β : Type} : List (α × β) -> List β
  | [] => []
  | (_, b) :: xs => b :: List.snds xs


def dx (n : Nat) : List (Int × Int) :=
  let rec go (n : Nat) (acc : List (Int × Int)) : List (Int × Int) :=
    match n with
    | 0 => acc
    | Nat.succ 0 => acc
    | Nat.succ n' => go n' ((n', 0) :: (-n', 0) :: acc)
  go (n + 1) []


def dy (n : Nat) : List (Int × Int) :=
  List.map Prod.swap (dx n)


def dxy (n : Nat) : List (Int × Int) :=
  let rec go (n : Nat) (acc : List (Int × Int)) : List (Int × Int) :=
    match n with
    | 0 => acc -- TODO: I shouldn't need this
    | Nat.succ 0 => acc
    | Nat.succ n' => go n'  ((n', n') :: (n', -n') :: (-n', n') :: (-n', -n') :: acc)
  go (n + 1) []


def deltas (x y xy : Nat) : List (Int × Int) :=
  dx x ++ dy y ++ dxy xy


def Piece.delta : Piece -> List (Int × Int)
  | Piece.king => deltas 1 1 1
  | Piece.queen => deltas 8 8 8
  | Piece.rook => deltas 8 8 0
  | Piece.bishop => deltas 0 0 8
  | Piece.knight => [(-2, -1), (-2, 1), (-1, -2), (-1, 2), (1, -2), (1, 2), (2, -1), (2, 1)] -- TODO: can rewrite as cartesian product
  | Piece.pawn => deltas 2 0 0


#eval Piece.pawn.delta


def neg? (x : Int) : Bool :=
  x < 0


def inBoard? (i j : Int) : Bool :=
  List.all [i, j] (λ x => 0 <= x && x < 8)


def getMoves (i j : Nat) (ds : List (Int × Int)) : List (Nat × Nat) :=
  let rec go (ds : List (Int × Int)) (acc : List (Nat × Nat)) : List (Nat × Nat) :=
    match ds with
    | [] => acc
    | (di, dj) :: ds =>
      let i' := i + di
      let j' := j + dj
      if inBoard? i' j' then
        go ds ((i'.toNat, j'.toNat) :: acc)
      else
        go ds acc
  go ds []


def Piece.moves (p : Piece) (i j : Nat) : List (Nat × Nat) :=
  getMoves i j p.delta


def Board.piece? (b : Board) (i j : Nat) : Bool :=
  match b[i][j]! with
  | none => false
  | _ => true


def abs (x : Int) : Int :=
  if x > 0 then x else (-x)


def inc (x : Int) : Int :=
  x + 1


def dec (x : Int) : Int :=
  x - 1


def pos? (x : Int) : Bool :=
  x > 0


def Nat.pos? (x : Nat) : Bool :=
  x > 0

-- TODO: extend to all types
def complement (f : Int -> Bool) : Int -> Bool :=
  λ x => !f x


def nonneg? : Int -> Bool :=
  complement neg?


def dist (x y : Nat) : Nat :=
  if x > y then
    x - y
  else
    y - x


def down (i j : Nat) : Nat × Nat :=
  (Nat.succ i, j)


def right (i j : Nat) : Nat × Nat :=
  (i, Nat.succ j)


def diag (i j : Nat) : Nat × Nat :=
  (Nat.succ i, Nat.succ j)


def blocks? (xss : Board) (i j : Nat) (n : Nat) (f : Nat → Nat → Nat × Nat) : Bool :=
  let rec go (i j : Nat) (n : Nat) : Bool :=
    match n with
    | 0 => false
    | Nat.succ n => match xss[i][j]! with
      | none =>
        let (i', j') := f i j -- TODO: remove this awkwardness
        go i' j' n
      | _ => true
  let (i', j') := f i j
  go i' j' n


def blockX? (xss : Board) (i j : Nat) (n : Nat) : Bool :=
  blocks? xss i j n right


-- TODO: refactor
def blockY? (xss : Board) (i j : Nat) (n : Nat) : Bool :=
  blocks? xss i j n down


def blockXY? (b : Board) (i j : Nat) (n : Nat) : Bool :=
  blocks? b i j n diag


def filterX (b : Board) (i j : Nat) (xs : List (Nat × Nat)) : List (Nat × Nat) :=
  let rec go (ms : List (Nat × Nat)) (acc : List (Nat × Nat)) : List (Nat × Nat) :=
    match ms with
    | [] => acc
    | (i', j') :: ms =>
      if i == i' then
        if blockX? b i (min j j') (dist j j') then
          go ms acc
        else
          go ms ((i', j') :: acc)
      else
        go ms ((i', j') :: acc)
  go xs []





def filterY (b : Board) (i j : Nat) (xs : List (Nat × Nat)) : List (Nat × Nat) :=
  let rec go (ms : List (Nat × Nat)) (acc : List (Nat × Nat)) : List (Nat × Nat) :=
    match ms with
    | [] => acc
    | (i', j') :: ms =>
      if j == j' then
        if blockY? b (min i i') j (dist i i') then
          go ms acc
        else
          go ms ((i', j') :: acc)
      else
        go ms ((i', j') :: acc)
  go xs []


-- TODO: I think this is wrong? Specifically the dist part
def filterXY (b : Board) (i j : Nat) (xs : List (Nat × Nat)) : List (Nat × Nat) :=
  let rec go (ms : List (Nat × Nat)) (acc : List (Nat × Nat)) : List (Nat × Nat) :=
    match ms with
    | [] => acc
    | (i', j') :: ms =>
      if (dist i i') == (dist j j') && (i < i' && j < j' || i > i' && j > j') then
        if blockXY? b (min i i') (min j j') (dist i i') then
          go ms acc
        else
          go ms ((i', j') :: acc)
      else
        go ms ((i', j') :: acc)
  go xs []


-- TODO: check super negative case
def blockXY'? (b : Board) (i j : Nat) (n : Nat) : Bool :=
  let rec go (i j : Nat) (n : Nat) : Bool :=
    match n with
    | 0 => false
    | Nat.succ n' => match b[i][j]! with
      | none => go (Nat.succ i) (j - 1) n'
      | _ => true
  go (Nat.succ i) (Nat.succ j) n


def filterXY' (b : Board) (i j : Nat) (xs : List (Nat × Nat)) : List (Nat × Nat) :=
  let rec go (ms : List (Nat × Nat)) (acc : List (Nat × Nat)) : List (Nat × Nat) :=
    match ms with
    | [] => acc
    | (i', j') :: ms =>
      if (dist i i') == (dist j j') && (i < i' && j > j' || i > i' && j < j') then
        if blockXY'? b (min i i') (max j j') (dist i i') then
          go ms acc
        else
          go ms ((i', j') :: acc)
      else
        go ms ((i', j') :: acc)
  go xs []


-- TODO: clean this up
-- TODO: add black/white and not taking your own piece
def Board.moves (b : Board) (i j : Nat) : List (Nat × Nat) :=
  match b[i][j]! with
  | none => []
  | some (c, p) =>
    let ms := p.moves i j
    match p with
    | Piece.king => ms
    | Piece.queen => ms |> filterY b i j |> filterX b i j |> filterXY b i j |> filterXY' b i j
    | Piece.rook => ms |> filterY b i j |> filterX b i j
    | Piece.bishop => ms |> filterXY b i j |> filterXY' b i j
    | Piece.knight => ms
    | Piece.pawn => ms


partial def Board.set_row (b : Board) (i : Nat) (row : List Square) : Board :=
  b.set i row


-- TODO: check
def Board.set (b : Board) (i j : Nat) (s : Square) : Board :=
  let row := b[i]!
  let row' := row.set j s
  b.set_row i row'


-- TODO: add features
def Board.show (b : Board) : IO Unit :=
  IO.println (Board.toString b)


-- TODO: case of moving to itself
def Board.move (b : Board) (x1 y1 : Nat) (x2 y2 : Nat) : Board :=
  let p := b[x1][y1]!
  let b' := b.set x2 y2 p
  b'.set x1 y1 none


#eval (b.move 6 3 4 3)
#eval blockX? (b.move 6 3 4 3) 4 0 3
#eval blocks? (b.move 6 3 4 3) 4 0 3 right



def Char.parseNat (c : Char) : Nat :=
  (c.toNat - '0'.toNat)


-- TODO: Should return an option
def parseMove (s : List Char) : Option (Nat × Nat) :=
  match s with
  | x :: ' ' :: y :: [] =>
    if x.isDigit && y.isDigit then
      (Char.parseNat x, Char.parseNat y)
    else
      none
  | _ => none


partial def loop (b : Board) : IO Unit := do
  let stdin ← IO.getStdin

  b.show

  let rec readInput (s : String) (ms : List (Nat × Nat)) : IO (Nat × Nat) := do
    match parseMove s.trim.toList with
    | some (i, j) => return (i, j)
    | none => do
      IO.println "x Invalid input. Please try again."
      IO.println ""
      b.show
      if ms ≠ [] then
        IO.println s!"> Available moves: {ms}"
      IO.print "> "
      let input ← stdin.getLine
      readInput input ms


  let rec read1 : IO (Nat × Nat) := do
    IO.print "Piece to move: "
    let input ← stdin.getLine
    let (i, j) <- readInput input []
    let ms := b.moves i j
    match ms with
    | [] => do
      b.show
      IO.println "x No moves available. Please try again."
      read1
    | ms => do
      IO.println s!"> Available moves: {ms}"
      return (i, j)

  let (i, j) ← read1
  let ms := b.moves i j

  let rec read2 : IO (Nat × Nat) := do
    IO.print "Move to: "
    let input ← stdin.getLine
    let (i', j') <- readInput input ms
    if (i', j') ∈ ms then
      return (i', j')
    else
      b.show
      IO.println s!"> Available moves: {ms}"
      IO.println "x Invalid move. Please try again."
      read2

  let (i', j') ← read2

  loop (b.move i j i' j')


def play : IO Unit := do
  loop Board.starting


def hello := "world"
