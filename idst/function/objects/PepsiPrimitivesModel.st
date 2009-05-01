" PepsiPrimitivesModel "

{ import: Objects }

Object perform: s with: a with: b with: c with: d with: e	{ _return(_sendv(v_s, 6, v_self, v_a, v_b, v_c, v_d, v_e)); }

Object perform: s with: a with: b with: c with: d with: e with: f	{ _return(_sendv(v_s, 7, v_self, v_a, v_b, v_c, v_d, v_e, v_f)); }

Object perform: s with: a with: b with: c with: d with: e with: f with: g	{ _return(_sendv(v_s, 8, v_self, v_a, v_b, v_c, v_d, v_e, v_f, v_g)); }


Object understands: selector
[
   | result current stop |
   current := self _vtable.
   result := nil.
   stop := Object _vtable delegate.
   [current ~= stop and: [result isNil]] whileTrue: [
       result := current findKeyOrNil: selector.
       current := current delegate.
   ].
   ^ result
]

"system call..."
OS system: _sysCall
{
    size_t size= (long)(((struct t_String *)v__sysCall)->v_size) >> 1;
    char *string= malloc(size + 1);
    memcpy(string, ((struct t_String *)v__sysCall)->v__bytes, size);
    string[size]= '\0';
    int r=system(string);
    _return (oop)r;
}

IdentityDictionary saveTo: aStream
[
    self do: [:assoc | aStream nextPutAll: assoc key; nextPut: $,; print: assoc value; cr]
]

IdentityDictionary loadFrom: aStream
[   | key value |
    [ aStream atEnd ]
        whileFalse:
           [ key := aStream upTo: $,.
             value := aStream upTo: $\n.
             self at: key asSymbol put: (Integer fromString: value) ].
]

Symbol copyFrom: s to: e
[ | res |
    res := ( String with: ( self at: s ) ) asSymbol.
    ( s + 1 ) to: e do: [:x | res := res , ( String with: ( self at: x ) ) asSymbol ].
    ^res
]

Number exp: i
[
    | res c |
    res := (1.0).
    c := 0.
    [ c < i ] whileTrue: 
      [ res := res * self. 
	c := c + 1 ].
    ^res
]

Symbol isCapitalized
[
    | fst |
    fst := self at: 0.
    ^( fst > 64 and: [ fst < 91 ] ).
]

Array shallowEq: anArray
[   
    self == anArray ifTrue: [^true].
    ( self size == anArray size ) ifFalse: [^false].
    self with: anArray do: [:a :b | a == b ifFalse: [^false]].
    ^true
]

Array toSymbolWithDelim: delim
[
    | index s res |
    res := delim asSymbol.
    s := self size.
    index := 0.
    [index < s ]
	whileTrue:
	   [ res := res , ( self at: index ) asSymbol.
	     index := index + 1 ].
    ^res
]

Array toIdentityDictionaryAsKeys
[
    | res |
    res := IdentityDictionary new.
    self do: [:itm | res at: itm put: true ].
    ^res
]

Array toIdentityDictionaryAsValuesStartAt: i
[
    | res |
    res := IdentityDictionary new.
    self do: [:itm | res at: i put: itm. i := i + 1 ].
    ^res
]

" ((a b) (1 2)) --> { a->1, b->2} "
Array keyValsToIdentityDictionary
[
    | res keys vals i |
    res := IdentityDictionary new. 
    keys := self at: 0.
    vals := self at: 1.
    i := 0. 
    keys do: [:k | res at: k put: ( vals at: i ). i := i + 1 ].
    ^res
]

SequenceableCollection sum
[ | res |
  res := 0.
  self do: [:itm | res := res + itm ].
  ^res
]

SequenceableCollection depth2Copy
[
    | res d |
    res := self new: ( self size ).
    d := 0.
    self do: [:n | res at: d put: ( n depth1Copy ). d := d + 1 ].
    ^res
]

SequenceableCollection depth1Copy
[
    | res t d i |
    res := self new: ( self size ).
    d := 0.
    self do: [:n1 | ( n1 isSequenceableCollection ) 
	              ifTrue: [  t := self new: ( n1 size ). 
			         i := 0.
			         n1 do: [:n2 | t at: i put: n2. i := i + 1 ] ]
	              ifFalse: [ t := n1 ].
                   res at: d put: t.
	           d := d + 1 ].
    ^res
]

SequenceableCollection toIdentityDictionaryAsValuesStartAt: i
[
    ^( ( Array withAll: self ) toIdentityDictionaryAsValuesStartAt: i )
]

SequenceableCollection toIdentityDictionaryAsKeys
[
    ^( ( Array withAll: self ) toIdentityDictionaryAsKeys )
]

SequenceableCollection keyValsToIdentityDictionary
[
    ^( ( Array withAll: self ) keyValsToIdentityDictionary )
]

IdentityDictionary merge: aDic
[ 
    aDic ifTrue: [ aDic keys do: [:k | self at: k put: ( aDic at: k ) ] ].
    ^self
]

IdentityDictionary merged: aDic
[
    | res |
    res := self new.
    ( self keys ) do: [:k | res at: k put: ( self at: k ) ].
    aDic ifTrue: [ aDic keys do: [:k | res at: k put: ( aDic at: k ) ] ].
    ^res
]

IdentityDictionary copy
[
    | res |
    res := self new.
    ( self keys ) do: [:k | res at: k put: ( self at: k ) ].
    ^res
]

OrderedCollection withAll: c1 withAll: c2
[
    ^( (self withAll: c1) addAll: c2 )
]

OrderedCollection map: unaryBlock
[
    | index res | 
    res := self new.
    index := firstIndex.
    [index < lastIndex]
	whileTrue:
	   [res add: ( unaryBlock value: (array at: index)).
	    index := index + 1].
    ^res
]

Array map: unaryBlock
[
    | index s res |
    s := self size.
    res := self new: s.
    index := 0.
    [index < s ]
	whileTrue:
	   [ res at: index put: ( unaryBlock value: ( self at: index ) ).
	     index := index + 1 ].
    ^res
]

"
;; returns a new list with elements of cross product of this and that list
;; [a b] [2 3] --> [[a 2] [a 3] [b 2] [b 3]]
"
OrderedCollection * c2
[   | res i j cs s |
    res := self new.
    s := self size.
    cs := c2 size.
    i := 0.
    [ i < s ] whileTrue:
      [ j  := 0.
        [ j < cs ] whileTrue:
	  [ res add: ( self with: ( self at: i ) with: ( c2 at: j ) ).
             j := j + 1 ].
	i := i + 1
      ].
    ^res
] 

"
;; [[a b]] --> [[a] [b]]
;; [[a b] [2 3]] --> [[a 2] [a 3] [b 2] [b 3]]
;; [[0 1] [a b] [2 3]] --> [[0 a 2] [0 a 3] ... ]
"
Array crossProduct
[
	| res n |
	self isEmpty ifTrue: [^ self].
	n := self inject: 1 into: [:s :c | s := s * c size].
        res := Array new: n.
	0 to: n - 1 do: [:i |
		| t elm |
	       elm := Array new: self size.
		t := i.
		0 to: self size - 1 do: [:j |
			| listItm |
			listItm := self at: j.
			elm at: j put: (listItm at: t \\ listItm size).
			t := t // listItm size.
		].
		res at: i put: elm
	].
       ^res
]

Array crossProductDo: aBlock
[
"
#((1 2) (3 4) (5 6) (a b c d)) crossProductDo: [:xs | self perform: #bla withArguments: xs ]
"

	| n arg |
	self isEmpty ifTrue: [^ self].
	arg := Array new: self size.
	n := self inject: 1 into: [:s :c | s := s * c size].
	0 to: n - 1 do: [:i |
		| t |
		t := i.
		0 to: self size - 1 do: [:j |
			| argValues |
			argValues := self at: j.
			arg at: j put: (argValues at: t \\ argValues size).
			t := t // argValues size.
		].
		aBlock value: arg		
	].
]

Array crossProductSelect: aBlock
[
"
#((1 2) (3 4) (5 6) (a b c d)) crossProductSelect: [:xs | xs second > 3 ]
] 
"
	| res n |
	self isEmpty ifTrue: [^ self].
        res := OrderedCollection new.
	n := self inject: 1 into: [:s :c | s := s * c size].
	0 to: n - 1 do: [:i |
		| t arg |
	        arg := Array new: self size.
		t := i.
		0 to: self size - 1 do: [:j |
			| argValues |
			argValues := self at: j.
			arg at: j put: (argValues at: t \\ argValues size).
			t := t // argValues size.
		].
		( aBlock value: arg ) ifTrue: [ res add: arg ]
	].
        ^res asArray
]

Object printlnMe
[
     self asString putln
]

Object printMe
[
     self asString put
]

SequenceableCollection firsts
[
    ^self firstsSecondsHelper: 0
]

SequenceableCollection seconds
[
    ^self firstsSecondsHelper: 1
]

SequenceableCollection firstsSecondsHelper: n
[
    | res |
    res := self new.
    self do: [:itm | res add: ( itm at: n ) ].
    ^res
]


Array firsts
[
    ^self firstsSecondsHelper: 0
]

Array seconds
[
    ^self firstsSecondsHelper: 1
]

Array firstsSecondsHelper: n
[
    | res i |
    res := self new: ( self size ).
    i := 0.
    self do: [:itm | res at: i put: ( itm at: n ). 
	             i := i + 1 ].
    ^res
]

OrderedCollection printlnMe
[
    self printlnMeHelper: true boundSyms: ( Array with: '[' with: ']' )
]

OrderedCollection printMe
[
    self printlnMeHelper: false boundSyms: ( Array with: '[' with: ']' )
]

OrderedCollection printlnMeHelper: nl boundSyms: bs
[
    | pComma |
    pComma := false.
    bs first put.
    ' ' put.
    self do: [:itm | pComma ifTrue: [ ', ' put ] ifFalse: [ pComma := true ]. itm printMe ]. 
    ' ' put.
    nl ifTrue: [ bs second putln ] ifFalse: [ bs second put ]
]

Array printlnMe
[
    self printlnMeHelper: true boundSyms: ( Array with: '[' with: ']' )
]

Array printMe
[
    self printlnMeHelper: false boundSyms: ( Array with: '[' with: ']' )
]

Array printlnMeHelper: nl boundSyms: bs
[
    | pComma |
    pComma := false.
    bs first put.
    ' ' put.
    self do: [:itm | pComma ifTrue: [ ', ' put ] ifFalse: [ pComma := true ]. itm printMe ]. 
    ' ' put.
    nl ifTrue: [ bs second putln ] ifFalse: [ bs second put ]
]

Boolean : Object (value)
Boolean value: val [ value := val ]
Boolean value [ ^value ]
Boolean isTrue [ ^value = #true ]
Boolean isFalse [ ^value = #false ]
Boolean isNil [ ^value isNil ]
Boolean print [ ^value print ]
