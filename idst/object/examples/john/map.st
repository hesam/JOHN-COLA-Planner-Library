{ import: Object }
{ import: John }

"
 This is an example of a Map object using the JOHN Planner to solve its Map Coloring problem:

 - The Map object passes JOHN the methods representing its goal (colored), 
   action (paint), types for action arguments ([Peice, Color]), 
   the paint action optimization method (paint_optimization),
   along with a copy of its current World;
 - JOHN will reason about the world, and return back a solution World (if one exisists),
 which Map can commit to if it wishes.
 
"

Map : ObjectPlus (pieces)
Piece : ObjectPlus (color neighbors)
Color : ObjectPlus ()

" intializes classes, making a collection to keep track of instanciated objects of each type: "
[ Map inits ]
[ Piece inits ]
[ Color inits ]

Map pieces: thePieces [ pieces := thePieces ]
Map pieces [ ^pieces ]

Map uncoloredPieces 
[ | res |
  res := OrderedCollection new.
  ( self pieces ) do: [:aPiece | ( aPiece color ) ifFalse: [ res add: aPiece ] ].
  ^res
]

Map draw
[
  '' putln. 'piece   color' putln. '-----   -----' putln.
  ( self pieces ) do: [:aPiece | ' ' put. aPiece print. '      ' put. aPiece color println. ].
  '' putln.
]

" * actions * "
Map paint: aPiece color: aColor
[
    ( aPiece colorable: aColor ) 
       ifTrue: [ aPiece color: aColor ] 
      ifFalse: [ ^false ].
    ^true
]

Map paint: a color: b _argTypes: c [ ^(Array with: Piece with: Color) ]

Map paint: aPiece color: aColor _optimization: c
[   
    ^( aPiece = self uncoloredPieces first )
]

" * goal * "
Map colored
[ 
  ( self pieces ) do: [:aPiece | ( aPiece color ) ifFalse: [ ^false ] ].
  ^true
]

" * world * 
  : object snapshot world (not needed when Worlds are implemented) "
Map worldSnapshot
[ | world |
  world := IdentityDictionary new.
  ( self pieces ) do: [:aPiece | world at: aPiece put: (aPiece color) ].
  ^world
]

" object world commit (not needed with Worlds) "
Map commitToWorld: world
[ 
  ( self pieces ) do: [:aPiece | aPiece color: (world at: aPiece) ].
  ^true
]

Piece neighbors: theNeighbors [ neighbors := theNeighbors ]
Piece color: aColor [ color := aColor ]
Piece color [ ^color ]
Piece neighbors [ ^neighbors ]

Piece colorable: aColor
[ ^( self color not and: 
     [ ( self neighbors ) do: [:aPiece | ( aPiece color == aColor ) ifTrue: [ ^false ] ].
       true ] )
]

" Main Program "
"
--------------------------------------
|                                  P6|
|  Green                             |
|     -------------------------      |
|     |                     P1|      |
|     |         Red           |      |
|     -------------------     |      |
|     |P2   |         P3|     |      |
|     |     |   Green   |     |      |
|     |     |     -------------      |
|     |     |     |P4         |      |
|     |     |     |   Yellow  |      |
|     |     -------------------      |
|     |  Blue           |   P5|      |
|     |                 |     |      |
|     ------------------|     |------|
|     |                       |      |
 -----|         Red           |      |
|     ------------------------       |
|                                    |
|P7                    Blue          |
-------------------------------------|
"

" Map can pass its current World, JOHN returns the solution World, which Map can commit to... "

[ | Red Blue Green Yellow P1 P2 P3 P4 P5 P6 P7 Puzzle solutionWorld |
  Red := Color new: #Red type: Color.
  Blue := Color new: #Blue type: Color.
  Green := Color new: #Green type: Color.
  Yellow := Color new: #Yellow type: Color.
 
  P1 := Piece new: #P1 type: Piece.
  P2 := Piece new: #P2 type: Piece.
  P3 := Piece new: #P3 type: Piece.
  P4 := Piece new: #P4 type: Piece.
  P5 := Piece new: #P5 type: Piece.
  P6 := Piece new: #P6 type: Piece.
  P7 := Piece new: #P7 type: Piece.
  P1 neighbors: (OrderedCollection new add: P2; add: P3; add: P4; add: P6; yourself).
  P2 neighbors: (OrderedCollection new add: P1; add: P3; add: P4; add: P5; add: P6; yourself).
  P3 neighbors: (OrderedCollection new add: P1; add: P2; add: P4; yourself).
  P4 neighbors: (OrderedCollection new add: P1; add: P2; add: P3; add: P5; add: P6; yourself).
  P5 neighbors: (OrderedCollection new add: P2; add: P4; add: P6; add: P7; yourself).
  P6 neighbors: (OrderedCollection new add: P1; add: P2; add: P4; add: P5; add: P7; yourself).
  P7 neighbors: (OrderedCollection new add: P4; add: P5; add: P6; yourself).
  Puzzle := Map new: #Puzzle type: Map.
  Puzzle pieces: (OrderedCollection new add: P1; add: P2; add: P3; add: P4; 
                                        add: P5; add: P6; add: P7; yourself).

  'Before:' putln.
  Puzzle draw.  
  "Puzzle paint: P5 color: Blue."
  solutionWorld := John forObject: Puzzle satisfyGoal: #colored 
		      withActions: #(paint:color:) options: #(Debug).
  solutionWorld ifTrue: [ Puzzle commitToWorld: solutionWorld ].  
  'After:' putln.
  Puzzle draw.
]


" Sample Output: 

Before:

piece   color
-----   -----
 P1      nil
 P2      nil
 P3      nil
 P4      nil
 P5      nil
 P6      nil
 P7      nil

After:

piece   color
-----   -----
 P1      Red
 P2      Blue
 P3      Green
 P4      Yellow
 P5      Red
 P6      Green
 P7      Blue

"
