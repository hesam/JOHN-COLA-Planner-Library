{ import: Object }
{ import: John }

Maze : ObjectPlus (robot size goalSquare squares squaresDic deltaRows deltaCols)
Robot : ObjectPlus (position)
Square : ObjectPlus (col row blocked)

" intializes classes, making a collection to keep track of instanciated objects of each type: "
[ Maze inits ]
[ Robot inits ]
[ Square inits ]

Robot position [ ^position ]
Robot position: aSquare [ position := aSquare ]

Square col: aCol row: aRow blocked: isBlocked
[ 
    col := aCol.
    row := aRow.  
    blocked := isBlocked
]

Square isBlocked [ ^blocked ]
Square blocked: isBlocked [ blocked := isBlocked ]
Square col [ ^col ]
Square row [ ^row ]

Maze robot: aRobot size: aSize
[   
    size := aSize.
    robot := aRobot.
    squaresDic := IdentityDictionary new.
    deltaRows := IdentityDictionary new.
    deltaCols := IdentityDictionary new.
    squares := Array new: size.
    0 to: ( size - 1 ) do: [:r | squares at: r put: ( Array new: size ) ].
    deltaRows at: #up put: 1.
    deltaRows at: #dn put: -1.
    deltaRows at: #lf put: 0.
    deltaRows at: #rt put: 0.
    deltaCols at: #up put: 0.
    deltaCols at: #dn put: 0.
    deltaCols at: #lf put: -1.
    deltaCols at: #rt put: 1.
]

Maze goalSquare: aSquare [ goalSquare := aSquare ] 
Maze robot [ ^robot ]
Maze size [ ^size ]
Maze squares [ ^squares ]
Maze squaresDic [ ^squaresDic ]

Maze neighborOf: sq direction: dir
[   | newRow newCol |
    newRow := sq row + ( deltaRows at: dir ).
    newCol := sq col + ( deltaCols at: dir ).
    ( newRow < 0 or: [ newRow > ( size - 1 ) ] ) ifTrue: [ ^false ].
    ( newCol < 0 or: [ newCol > ( size - 1 ) ] ) ifTrue: [ ^false ].
    ^( squares at: newRow ) at: newCol
]

"[ GOAL ]"
Maze win
[
    ^robot position = goalSquare
]

"[ Goal -> Heuristics ]"

"
Maze win_heuristic 
[
     ^( ( goalSquare row - robot position row ) abs + 
        ( goalSquare col - robot position col ) abs )
]
"

"[ ACTIONS ]"
Maze moveRobot: dir
[   | sqrTo sqrFrom |
    sqrFrom := robot position.
    sqrTo := self neighborOf: sqrFrom direction: dir.
    sqrTo ifFalse: [ ^false ].
    sqrTo isBlocked ifTrue: [ ^false ].
    robot position: sqrTo.
    ^true
]

"[ Action -> Arg Types ]"
Maze moveRobot: dir _argTypes: c [ ^#((up dn lf rt)) ]

"[ WORLD ]"
Maze worldSnapshot
[   | world |
    world := IdentityDictionary new.
    world at: #position put: ( robot position ).
    "world := robot position."
    ^world
]

" object world commit (not needed with Worlds) "
Maze commitToWorld: world
[ 
    robot position: ( world at: #position ).
"    robot position: world."

    ^true
]

" only needed if want to use learnings from one goal for different goals "
Maze win_worldSnapshot
[   | world |
    world := IdentityDictionary new.
    world at: #position put: goalSquare.
    'goal:' put. goalSquare println.
    ^world
]

Maze draw
[   | sqr |
    0 to: ( size - 1 ) do: 
     [:r | '---------------------------------' putln.
           0 to: ( size - 1 ) do: 
             [:c | sqr := ( squares at: ( ( size - 1 ) - r ) ) at: c.
                   '| ' put. 
                   ( ( sqr isBlocked )
                      ifTrue: [ 'X' ] 
	             ifFalse: [ sqr = robot position
                                   ifTrue: [ 'R' ] 
                                  ifFalse: [ sqr = goalSquare
                                                ifTrue: [ 'G' ] 
                                               ifFalse: [ ' ' ] ] ] ) put. 
             ' ' put ].
             '| ' put. 
             ( size - r ) println ].
    '---------------------------------' putln.
    '  A   B   C   D   E   F   G   H' putln
]

" Main Program "
[ | columns blocks startSquare goalSquare Robby Amaze solutionWorld |

  columns := #(A B C D E F G H).
  blocks := #(A6 B3 D2 D4 D7 E1 E4 F3 F5 F6 G2 G7 H4 H6).
  startSquare := #H1.
  goalSquare := #H8.

  Robby := Robot new: #Robby type: Robot.
  Amaze := Maze new: #Amaze type: Maze.
  Amaze robot: Robby size: 8.
  0 to: ( Amaze size - 1 ) do: [:c | 0 to: ( Amaze size - 1 ) do: 
    [:r | | newSqr newSqrName |
        newSqrName := (columns at: c) , ( r + 1 ).
        newSqr := Square new: newSqrName type: Square.
        newSqr col: c row: r blocked: false.
        Amaze squaresDic at: newSqrName put: newSqr.
        ( Amaze squares at: r ) at: c put: newSqr ] ].
  blocks do: [:blkSq | ( Amaze squaresDic at: blkSq ) blocked: true ].
  Amaze goalSquare: ( Amaze squaresDic at: goalSquare ).
  ( Amaze robot ) position: ( Amaze squaresDic at: startSquare ).

  'Before:' putln.
  Amaze draw.  
  solutionWorld := John forObject: Amaze satisfyGoal: #win 
		        withActions: #(moveRobot:) options: #(Debug).
  solutionWorld ifTrue: [ Amaze commitToWorld: solutionWorld ].  
  'After:' putln.
  Amaze draw.

]

  
" Sample Output "
"
w/o Heuristics
--------------

Before:
---------------------------------
|   |   |   |   |   |   |   | G | 8
---------------------------------
|   |   |   | X |   |   | X |   | 7
---------------------------------
| X |   |   |   |   | X |   | X | 6
---------------------------------
|   |   |   |   |   | X |   |   | 5
---------------------------------
|   |   |   | X | X |   |   | X | 4
---------------------------------
|   | X |   |   |   | X |   |   | 3
---------------------------------
|   |   |   | X |   |   | X |   | 2
---------------------------------
|   |   |   |   | X |   |   | R | 1
---------------------------------
  A   B   C   D   E   F   G   H
at depth 1 ... # possible worlds: 2
at depth 2 ... # possible worlds: 4
at depth 3 ... # possible worlds: 8
at depth 4 ... # possible worlds: 16
at depth 5 ... # possible worlds: 33
at depth 6 ... # possible worlds: 66
at depth 7 ... # possible worlds: 137
at depth 8 ... # possible worlds: 277
at depth 9 ... # possible worlds: 576
at depth 10 ... # possible worlds: 1185
at depth 11 ... # possible worlds: 2481
at depth 12 ... # possible worlds: 5227
at depth 13 ... # possible worlds: 11161
at depth 14 ... # possible worlds: 24320
at depth 15 ... # possible worlds: 54133
at depth 16 ... # possible worlds: 123760
at depth 17 ...

[ solution time: 23 sec ]

After:
---------------------------------
|   |   |   |   |   |   |   | R | 8
---------------------------------
|   |   |   | X |   |   | X |   | 7
---------------------------------
| X |   |   |   |   | X |   | X | 6
---------------------------------
|   |   |   |   |   | X |   |   | 5
---------------------------------
|   |   |   | X | X |   |   | X | 4
---------------------------------
|   | X |   |   |   | X |   |   | 3
---------------------------------
|   |   |   | X |   |   | X |   | 2
---------------------------------
|   |   |   |   | X |   |   |   | 1
---------------------------------
  A   B   C   D   E   F   G   H

w/ Heuristics
--------------

Before:
---------------------------------
|   |   |   |   |   |   |   | G | 8
---------------------------------
|   |   |   | X |   |   | X |   | 7
---------------------------------
| X |   |   |   |   | X |   | X | 6
---------------------------------
|   |   |   |   |   | X |   |   | 5
---------------------------------
|   |   |   | X | X |   |   | X | 4
---------------------------------
|   | X |   |   |   | X |   |   | 3
---------------------------------
|   |   |   | X |   |   | X |   | 2
---------------------------------
|   |   |   |   | X |   |   | R | 1
---------------------------------
  A   B   C   D   E   F   G   H
at threshold 9 ...
at threshold 11 ...
at threshold 13 ...
at threshold 15 ...
at threshold 17 ...
[ solution time: 2 sec ]

After:
---------------------------------
|   |   |   |   |   |   |   | R | 8
---------------------------------
|   |   |   | X |   |   | X |   | 7
---------------------------------
| X |   |   |   |   | X |   | X | 6
---------------------------------
|   |   |   |   |   | X |   |   | 5
---------------------------------
|   |   |   | X | X |   |   | X | 4
---------------------------------
|   | X |   |   |   | X |   |   | 3
---------------------------------
|   |   |   | X |   |   | X |   | 2
---------------------------------
|   |   |   |   | X |   |   |   | 1
---------------------------------
  A   B   C   D   E   F   G   H

"
