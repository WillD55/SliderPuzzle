open util/ordering[Board]


let SIZE = 3

let Row = { i: Int | 1 =< i and i =< SIZE }
let Col = { i: Int | 1 =< i and i =< SIZE }

sig Tile {}
	
one sig T1, T2, T3, T4, T5, T6, T7, T8, Blank extends Tile {}

sig Board {
	at: Row -> Col -> one Tile
}

pred BeginningBoard {
	first.at[1,1] = T5
	first.at[1,2] = T2
	first.at[1,3] = T1
	first.at[2,1] = Blank
	first.at[2,2] = T3
	first.at[2,3] = T4
	first.at[3,1] = T8
	first.at[3,2] = T7
	first.at[3,3] = T6
}
// [ 5, 2, 1, 
//   B, 3, 4, 
//   8, 7, 6 ]

run BeginningBoard for 1

pred EndingBoard {
	last.at[1,1] = T1
	last.at[1,2] = T2
	last.at[1,3] = T3
	last.at[2,1] = T4
	last.at[2,2] = T5
	last.at[2,3] = T6
	last.at[3,1] = T7
	last.at[3,2] = T8
	last.at[3,3] = Blank
}

run EndingBoard for 1

pred Neighbors [i1 : Row, j1 : Col, i2 : Row, j2 : Col] {
	(i1 = i2 and (j2 = add[j1,1] or j2 = sub[j1,1]))
	or
	(j1 = j2 and (i2 = add[i1,1] or i2 = sub[i1,1]))
} // checks up,down,left,right of a tile to find its neighbors

pred LegalMove [b1,b2 : Board] {
	some i1: Row, i2: Row, j1 : Col, j2: Col |
	b1.at[i1,j1] = Blank 
	and
	Neighbors[i1,j1,i2,j2]
	and
	b2.at[i1,j1] = b1.at[i2,j2]
	and 
	b2.at[i2,j2] = Blank
	and
	all r: Row, c: Col | not r -> c in (i1 -> j1 + i2 -> j2) implies
	b2.at[r, c] = b1.at[r, c]
//	all r: Row, c: Col | (r != i1 or c != j1) and (r != i2 or c != j2) implies 
//			b2.at[r, c] = b1.at[r, c]
}
// allows blank and neighbor to switch positions and no other tiles to move

pred Game {
	BeginningBoard
	all b: Board - last | LegalMove[b, b.next]
       EndingBoard
}

run Game for exactly 9 Tile, 46 Board
run Game for exactly 9 Tile, 20 Board
run Game for exactly 9 Tile, 34 Board
run Game for exactly 9 Tile, 22 Board
run Game for exactly 9 Tile, 24 Board //minimal solution

// minimal solution is 23 moves

assert NoReverse {
	Game 
	implies
	all b: Board | b.next.next != b
}

check NoReverse

assert Unique{
	Game
	implies
	all b: Board, t: Tile | one r: Row, c: Col | b.at[r, c] = t
	and
	all b: Board, r: Row, c: Col | one b.at[r, c]
}

check Unique






