{ import: Object }
{ import: John }

"
 This is an example of a TextBox object using the JOHN Planner to solve its text layout problem:
 "
TextBox : ObjectPlus (width words lines nextWordToLayoutIdx currLineBudget)
Word : ObjectPlus (symbol isPlaced)

" intializes classes, making a collection to keep track of instanciated objects of each type: "
[ TextBox inits ]
[ Word inits ]

Word isPlaced: placed [ isPlaced := placed ]
Word isPlaced [ ^isPlaced ]
Word symbol [ ^symbol ]
Word size [ ^symbol size ]
Word new: aName [ self := Word new. symbol := aName ]

TextBox new: aName width: aWidth words: theWords
[
    self := self new: aName type: TextBox.
    width := aWidth.
    currLineBudget := aWidth.
    nextWordToLayoutIdx := 0.
    lines := OrderedCollection with: ( OrderedCollection new ).
    words := OrderedCollection new.
    theWords do: [:w | words add: ( Word new: w ) ].
]

TextBox currLine [ ^lines last ]
TextBox nextWord [ ^words at: nextWordToLayoutIdx ]
TextBox newline [ currLineBudget := width. lines add: ( OrderedCollection new ) ]
TextBox allWordsPlaced [ words do: [:w | w isPlaced ifFalse: [ ^false ] ]. ^true ]

" [ GOAL ] "
TextBox layout [ ^self allWordsPlaced ]

" --> Goal OPTIMIZATION "
TextBox layout_optimization 
[ 
    ^( self nextWord size < width ) ifTrue: [ #(placeNextWord:) ] ifFalse: [ #(breakNextWord) ]
]

" [ ACTIONS ] "

" Action #1 "
TextBox placeNextWord: onNewLine
[ | word |
    word := self nextWord.
    onNewLine ifTrue: [ self newline ].
    self currLine add: word symbol.
    nextWordToLayoutIdx := nextWordToLayoutIdx + 1.
    currLineBudget := currLineBudget - word size - 1.
    word isPlaced: true.
    ^true
] 

" --> Action ARGTYPES "
TextBox placeNextWord: a _argTypes: b [ ^( Array with: ( Array with: true with: false ) ) ]

" --> Action OPTIMIZATION "
TextBox placeNextWord: onNewLine _optimization: b 
[   
    ^( self nextWord size < currLineBudget ) 
          ifTrue: [ onNewLine = false ] ifFalse: [ onNewLine = true ]
]

" Action #2 "
TextBox breakNextWord
[ | word s i w1 w2 |
    word := self nextWord symbol.
    s := word size.
    i := ( s - ( s \\ 2 ) ) / 2.
    w1 := Word new: ( ( word copyFrom: 0 to: i ) , '-' ).
    w2 := Word new: ( word copyFrom: ( i + 1 ) to: ( s - 1 ) ).
    words at: nextWordToLayoutIdx put: w1.
    words insert: w2 atIndex: (nextWordToLayoutIdx + 1).
    ^true    
]

TextBox draw
[
    1 to: width do: [:x | '.' put ]. '' putln.
    lines do: [:ln | ln do: [:wd | wd asString put. ' ' put ]. '' putln ].
    1 to: width do: [:x | '.' put ]. '' putln.
]

" Main Program "

[ | Text solutionWorld |

  Text := TextBox new: #Text width: 20 words: #(this is one too simplistic text box for sure but there is thisverygiganticword here that needs to be handled).
  'Before:' putln.
  Text draw.  
  solutionWorld := John forObject: Text satisfyGoal: #layout 
		      withActions: #(placeNextWord: breakNextWord) options: #(Debug).
  solutionWorld ifTrue: [ Text commitToWorld: solutionWorld ].
  'After:' putln.
  Text draw.
]


" Sample Output: 

Before:
....................

....................
After:
....................
this is one too 
simplistic text box 
for sure but there 
is thisverygig- 
anticword here that 
needs to be handled 
....................

"
