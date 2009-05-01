{ import: Object }
{ import: John }

"
 This is an example of a Allocator object using the JOHN Planner to solve its 
 Register Allocation problem:

 - The Allocator object passes JOHN the methods representing its goal (allocation), 
   possible an optimization method for the goal (allocation_optimization),
   actions (assign split), each action has a special method to get types for its 
   arguments ([[Register, Variable], [Register, Register]]), and possibly 
   optimization methods for each, along with a copy of its current World;
 - JOHN will reason about the world, and return back a solution World (if one exisists),
   which Allocator can commit to if it wishes.

 - X86 Registers:

   * Normal *

        EAX:17      ECX:20      EDX:22     ESI:25      EDI:21      EBX:19      EBP:18
    ----------- ----------- ----------- ----------- ----------- ----------- -----------
     AX:3        CX:11       DX:16       SI:84       DI:13       BX:8        BP:6
    -----       -----       -----       -----       -----       -----       -----       
  I AL AH       CL CH       DL DH       SIL         DIL         BL BH       

   * Floating Point *

      XMM0:96     XMM1:97     XMM2:104    XMM0:105    XMM0:106    XMM0:107   XMM0:108   
    ----------- ----------- ----------- ----------- ----------- ----------- -----------

   * Pseudo Floating Point *

      FP0: 27     FP1: 28     FP2: 29     FP3: 30      FP4: 31    FP5: 32     FP6: 33
    ----------- ----------- ----------- ----------- ----------- ----------- -----------

    0:NOREG 1:AH    2:AL    3:AX    4:BH    5:BL    6:BP    7:BPL   8:BX    9:CH    10:CL   
    11:CX   12:DH   13:DI   14:DIL  15:DL   16:DX   17:EAX  18:EBP  19:EBX  20:ECX  21:EDI  
    22:EDX  23:EFLAGS       24:EIP  25:ESI  26:ESP  27:FP0  28:FP1  29:FP2  30:FP3  31:FP4  
    32:FP5  33:FP6  34:IP   35:MM0  36:MM1  37:MM2  38:MM3  39:MM4  40:MM5  41:MM6  42:MM7  
    43:R10  44:R10B 45:R10D 46:R10W 47:R11  48:R11B 49:R11D 50:R11W 51:R12  52:R12B 53:R12D 
    54:R12W 55:R13  56:R13B 57:R13D 58:R13W 59:R14  60:R14B 61:R14D 62:R14W 63:R15  64:R15B 
    65:R15D 66:R15W 67:R8   68:R8B  69:R8D  70:R8W  71:R9   72:R9B  73:R9D  74:R9W  75:RAX  
    76:RBP  77:RBX  78:RCX  79:RDI  80:RDX  81:RIP  82:RSI  83:RSP  84:SI   85:SIL  86:SP   
    87:SPL  88:ST(0)        89:ST(1)        90:ST(2)        91:ST(3)        92:ST(4)        
    93:ST(5)        94:ST(6)        95:ST(7)        96:XMM0 97:XMM1 98:XMM10        99:XMM11
    100:XMM12       101:XMM13       102:XMM14       103:XMM15       104:XMM2        
    105:XMM3        106:XMM4        107:XMM5        108:XMM6        109:XMM7        110:XMM8
    111:XMM9

variables/registers:
 Variable        class         puzzleType        length(bytes)    category
 32-bit           6                 2              4                1
 16-bit           4                 2              2                1
 8-bit            9                 1              1                1


 float(128-bit?)  2                 4              16               2
 float(128-bit?)  3                 4              16               2
 pseudo-float     11                4              ?                3

banks:        category
general        1
fp1            2
fp2            3

"
Allocator : ObjectPlus (banks banksDic registers variables allocatedRegs unassignedVars 
                        spilledVars varNToSplit classToLengthMap classToCategoryMap 
                        programSize)
Variable : ObjectPlus (length category number liveRanges usedAtInsts fixedAtInsts 
                       assigned assignedRegs)
RegBank : ObjectPlus (section category index allocations)
Register : ObjectPlus (length category number banks)

Object HS_Allocator_run
[
    ^42
]

Object HS_Allocator_Allocator_newWithProgramSize: arg1
[
    ^Allocator newWithProgramSize: arg1
]

Allocator newWithProgramSize: numInsts
[   | X86Regs |

    " intializes classes, making a collection to keep track of instanciated objects
      of each type: "
    Allocator inits.
    Variable inits.
    RegBank inits.
    Register inits.

    self := Allocator new.
    name := #Al.
    programSize := numInsts.
    allocatedRegs := IdentityDictionary new.
    banksDic := IdentityDictionary new.
    banks := OrderedCollection new.
    registers := IdentityDictionary new.
    variables := IdentityDictionary new.
    unassignedVars := OrderedCollection new.
    spilledVars := IdentityDictionary new.
    classToLengthMap := IdentityDictionary new.
    classToCategoryMap := IdentityDictionary new.
    #((2 16 2) (3 16 2) (4 2 1) (6 4 1) (9 1 1) (11 16 3)) do: 
      [:x | classToLengthMap at: (x first) put: (x second).
            classToCategoryMap at: (x first) put: (x third) ].

    Allocator addInstance: self.
      
    " Register Banks "
    0 to: 31 do: [:n | ( n < 16 or: [ n > 19 ] ) ifTrue: 
      [ self newRegBank: ( #R , n ) category: 1 
             section: ( n \\ 2 == 0 ifTrue: [ #low ] ifFalse: [ #high ] ) index: n ] ].
    #((2 32 38) (3 39 45)) do: 
    [:x | ( x second ) to: ( x third ) do: 
      [:n | self newRegBank: ( #R , n ) category: ( x first ) 
                            section: #high index: n ] ].

    X86Regs :=
         " 32-bit regs in order "
    #((1 ((EAX 4 17 (R3 R2 R1 R0)) (ECX 4 20 (R11 R10 R9 R8)) 
	  (EDX 4 22 (R15 R14 R13 R12)) (ESI 4 25 (R27 R26 R25 R24)) 
          (EDI 4 21 (R31 R30 R29 R28)) (EBX 4 19 (R7 R6 R5 R4))
          (EBP 4 18 (R23 R22 R21 R20))
         " 16-bit regs in order "
          (AX 2 3 (R1 R0)) (CX 2 11 (R9 R8)) (DX 2 16 (R13 R12)) (SI 2 84 (R25 R24))
          (DI 2 13 (R29 R28)) (BX 2 8 (R5 R4)) (BP 2 6 (R21 R20))
         " 8-bit regs in order "
          (AL 1 2 (R0)) (CL 1 10 (R0)) (DL 1 15 (R0)) (BL 1 5 (R0))
          (AH 1 1 (R0)) (CH 1 9 (R0)) (DH 1 12 (R0)) (BH 1 4 (R0))))
         " Floating point Regs in order "
      (2 ((XMM0 16 96 (R32)) (XMM1 16 97 (R33)) (XMM2 16 104 (R34)) (XMM3 16 105 (R35))
          (XMM4 16 106 (R36)) (XMM5 16 107 (R37)) (XMM6 16 108 (R38))))
         " Pseudo-Floating point Regs in order "
      (3 ((FP0 16 27 (R39)) (FP1 16 28 (R40)) (FP2 16 29 (R41)) (FP3 16 30 (R42))
          (FP4 16 31 (R43)) (FP5 16 32 (R44)) (FP6 16 33 (R45))))).

    X86Regs do: 
      [:x | | category regs |
        category := x first. 
        regs := x second.
        regs do: 
          [:r | self newRegister: ( r first ) length: ( r second ) 
                     category: category number: ( r third ) banks: ( r fourth ) ] ].

]

" fixme "
Allocator register: regNum allocationAt: idx 
[   | alloc |
    ( (registers at: regNum) banks first hasAllocationAtIdx: idx ) ifFalse: [ ^nil ].
    alloc := (registers at: regNum) banks first allocations at: idx.
    ( alloc length = (registers at: regNum) length ) ifTrue: [ ^alloc number ]
                                                    ifFalse: [ ^nil ]
]

" idx should be a beg of instruction index: should be multiple of 2 "
Allocator allocationsAt: idx
[   | res |
    res := IdentityDictionary new.
    allocatedRegs keys do: [:regN | | q1 q2 |
			     q1 := self register: regN allocationAt: idx.
			     q2 := self register: regN allocationAt: idx + 1.
                             q1 ifTrue: [ res at: q1 put: regN ].
                             q2 ifTrue: [ res at: q2 put: regN ] ].
    ^res
]
 
Allocator unassignedVars: theVars 
[ 
    unassignedVars := OrderedCollection withAll: theVars 
]

Allocator banks [ ^banks ]
Allocator registers [ ^registers ]
Allocator allocatedRegs [ ^allocatedRegs ]
Allocator variables [ ^variables ]
Allocator unassignedVars [ ^unassignedVars ]
Allocator spilledVars [ ^spilledVars ]
Allocator programSize [ ^programSize ]

Allocator draw
[
  '' putln.
  '       EAX:17      EBX:19      ECX:20     EDX:22      EBP:18      ESI:25      EDI:21' putln.
  '    ----------- ----------- ----------- ----------- ----------- ----------- -----------' putln.
  '     AX:3        BX:8       CX:11       DX:16        BP:84       SI:6       DI:13' putln. 
  '    -----       -----       -----       -----       -----       -----       -----       ' putln. 
  '  I AL AH       BL BH       CL CH       DL DH       BPL         SIL         DIL' putln.
  '    ' put.
  0 to: 31 do: [:n | ( n < 16 or: [ n > 19 ] ) ifTrue: [ n symbol1 put. ' ' put ] ].
  '' putln.
  0 to: programSize * 2 - 1 do: 
    [:idx | ((idx \\ 2) == 0) ifTrue: [ '.......................................................................................' putln ].
	    (idx * 2) symbol put. 
            self banks do: [:bank | (bank category ~= 3) ifTrue: [ ' ' put. (bank allocations at: idx) symbol put ] ].
            '' putln ].
  spilledVars keys size > 0 ifTrue: [ '--> spilled vars:  ' put. spilledVars println ].
  unassignedVars size > 0 ifTrue: [ ' -> next: ' put. unassignedVars first print. ' ... ' put.  unassignedVars first liveRanges print. ' fixedAt: ' put. unassignedVars first fixedAtInsts println  ]
]

" qualifications "
Integer symbol 
[   | spc | 
    spc := self < 10 ifTrue: [ '  ' ] 
                    ifFalse: [ self < 100 ifTrue: [ ' ' ] ifFalse: [ '' ] ].  
    ^spc , self asString
]

Integer symbol1 
[ 
    ^( self < 10 ifTrue: [ ' ' , self asString ] ifFalse: [ self asString ] ) 
]

UndefinedObject symbol [ ^'--' ]
Variable symbol [ ^(self number \\ 1000) asString ]
Symbol symbol [ ^self = #precolored ifTrue: [ 'XX' ] ifFalse: [ self asString ] ]
Integer asAllocationIndex [ ^self / 2 ]
Integer asIntervalIndex [ ^self * 2 ]
Integer asInstIdxStart [ ^self - (self \\ 4) ]

Array atInterval: intv put: val
[
    intv first to: (intv second - 1) do: 
      [:i | self at: (i asAllocationIndex) put: val ]
]

RegBank freeAtInterval: intv
[
    intv first to: (intv second - 1) do: 
      [:i | (self allocations at: (i asAllocationIndex)) ifTrue: [ ^false ] ].
    ^true
]

RegBank freeUpIntervals: intvs
[
    intvs do: [:intv |
      intv first to: (intv second - 1) do: 
        [:i | self allocations at: (i asAllocationIndex) put: nil] ].
    ^true
]

Allocator canAllocate: var allRanges: doAllRanges
[
    registers keys do: 
      [:regN | ( ( registers at: regN ) canAllocate: var allRanges: doAllRanges ) 
                 ifTrue: [ ^true ] ].
    ^false
]

Allocator regToAllocate: var allRanges: doAllRanges
[
    registers keys do: 
      [:regN | ( ( registers at: regN ) canAllocate: var allRanges: doAllRanges ) ifTrue: 
                 [ ^registers at: regN ] ].
    ^false
]

Allocator spillRequired: var
[
    var liveRanges do: 
      [:lRange | 
        ( self anyBanksFreeAtIdxRangeFrom: (lRange first asAllocationIndex) 
	       to: ((lRange second - 2) asAllocationIndex) var: var )
          ifFalse: [ 'spill required for: ' put. var print. ' spilling: ' put. varNToSplit print. ' at ' put. ( spilledVars at: varNToSplit ) println. 
          'picked: ' put. varNToSplit print. ' liveRange: ' put. (variables at: varNToSplit) liveRanges print. ' fixedAt: ' put. (variables at: varNToSplit) fixedAtInsts print. ' usedAt: ' put. (variables at: varNToSplit) usedAtInsts println.
          ^true ] ].
    ^false
]

Allocator anyBanksFreeAtIdxRangeFrom: s to: e var: var
[
    s to: e do: [:idx | ( self anyBanksFreeAtIdx: idx var: var ) ifFalse: 
      [ | instIdx |
        instIdx := idx asIntervalIndex asInstIdxStart.
        varNToSplit := self findVarToSpillAt: instIdx 
	                    checkLiveIntervals: ( unassignedVars first liveRanges ).
        spilledVars at: varNToSplit put: 
          ( ( var number = varNToSplit ) ifTrue: [ instIdx ] 
	                                ifFalse: [ s asIntervalIndex asInstIdxStart ] ).
	^false ] ].
    ^true            
]

Allocator anyBanksFreeAtIdx: idx var: var
[
    banks do: [:bank | ( ( bank category = var category ) and: 
                         [ bank freeAtIdx: idx ] ) ifTrue: [ ^true ] ].
    ^false
]

Register canAllocate: var allRanges: doAllRanges
[   | ranges |
    ( category = var category ) ifFalse: [ ^false ].
    ( length = var length ) ifFalse: [ ^false ].
    ranges := ( doAllRanges ifTrue: [ var liveRanges ] 
	                   ifFalse: [ OrderedCollection with: ( var liveRanges first ) ] ).
    banks do: [:bank | ranges do: 
      [:lRange | ( bank freeAtInterval: lRange ) ifFalse: [ ^false ] ] ].
    ^true
]

Register deallocateIntervals: intvs
[
    banks do: [:bank | bank freeUpIntervals: intvs ].
    ^true
] 

Allocator precolor: regNum intervalStart: intvS intervalEnd: intvE
[
    (registers includesKey: regNum) ifFalse: [ ^false ]. " fixme: no FPX yet... "
    (registers at: regNum) banks do:
      [:bank | bank allocations atInterval: (Array with: intvS with: intvE) 
	                               put: #precolored ].
    ^true
]


" [ GOAL ] "
Allocator allocation [ ^unassignedVars size = 0 ]

" [ GOAL OPTIMIZATION ] "
Allocator allocation_optimization
[
    | var |
    var := unassignedVars first.
    ^( Array with: ( ( self canAllocate: var allRanges: false ) 
                      ifTrue: [ #assign:var:allRanges: ] 
                     ifFalse: [ ( self spillRequired: var ) 
                                   ifTrue: [ #spill: ]
                                  ifFalse: [ #split:to: ] ] ) )
]

" [ ACTIONS ] "
Allocator assign: reg var: var allRanges: doAllRanges
[   | ranges |    
    'in assign - ' put. reg print. ' ' put. var print. ' ' put. doAllRanges println.
    var isAssigned ifTrue: [ ^false ].
    ( reg canAllocate: var allRanges: doAllRanges ) ifFalse: [ ^false ].
    ranges := doAllRanges ifTrue: [ var liveRanges ] 
	                 ifFalse: [ OrderedCollection with: ( var liveRanges first ) ].
    ranges do:
      [:intv | reg banks do: [:bank | bank allocations atInterval: intv put: var ] ].
    doAllRanges ifTrue: [ self unassignedVars remove: var ifAbsent: false ]
                ifFalse: [ var removeFirstLiveRange ].
    allocatedRegs at: (reg number) put: true.
    var assignedRegs at: (reg number) put: reg.
    'assigned: ' put. var println. ' for ' put. ranges println.
    self draw.
    ^true 
]

Allocator split: regBankFrom to: regBankTo 
[ | intv splitIntv idx |
    regBankFrom = regBankTo ifTrue: [ ^false ].
    ( regBankFrom section = #high and: [ regBankTo section = #low ] ) 
      ifFalse: [ ^false ].
    unassignedVars first liveRanges size = 1 ifFalse: [ ^false ].
    intv := unassignedVars first liveRanges first.
    ( regBankFrom allocations at: (intv first asAllocationIndex) ) ifFalse: [ ^false ].
    ( regBankFrom allocations at: (intv first asAllocationIndex) ) = #precolored 
      ifTrue: [ ^false ].
    splitIntv := Array with: intv first - 2 
                       with: ((regBankFrom allocations at: 
      (intv first asAllocationIndex)) liveRanges first second).
    ( regBankTo freeAtInterval: splitIntv) ifFalse: [ ^false ].    
    splitIntv first to: splitIntv second do: 
      [:i | idx := i asAllocationIndex. 
            regBankTo allocations at: idx put: (regBankFrom allocations at: idx) ].
    regBankFrom allocations atInterval: splitIntv put: nil.
    ^true
]

Allocator spill: var
[
    " cut live ranges short for var and re-attempt allocation: "
    var cutLiveRangesAndSelfDeallocateForSpillAt: ( spilledVars at: ( var number ) ).
    'spilled: ' put. var println.
    self draw.
    ^true
]

" [ ACTION ARG TYPES ] "
Allocator assign: a var: b allRanges: c _argTypes: d [ ^Array with: Register with: Variable with: (Array with: true with: false) ]
Allocator split: a to: b _argTypes: c [ ^Array with: RegBank with: RegBank ]
Allocator spill: a _argTypes: b [ ^Array with: Variable ]

" [ ACTION OPTIMIZATION ] "
Allocator assign: reg var: var allRanges: doAllRanges _optimization: c
[    
    ^( ( var = unassignedVars first and: [ var length = reg length ] ) and:
         [ var category = reg category ] ) and: 
           [ ( doAllRanges = ( self canAllocate: var allRanges: true ) ) and:
             [ reg = ( self regToAllocate: var allRanges: doAllRanges ) ] ] " <--- 2nd line fixme " 
]

Allocator spill: var _optimization: c 
[ 
    ^var number = varNToSplit
]


" object snapshot world (not needed with Worlds) "
Allocator worldSnapshot
[ | world res |
  world := IdentityDictionary new.
  world at: #Variables put: IdentityDictionary new.
  world at: #RegBanks put: IdentityDictionary new.
  world at: #unassignedVars put: ( unassignedVars copy ).
  world at: #spilledVars put: ( spilledVars copy ).
  variables keys do: 
    [:varN | (world at: #Variables) at: varN put: (variables at: varN) isAssigned ].
  banks do: [:bank | (world at: #RegBanks) at: bank put: bank allocations copy ].
  ^world
]

" object world commit (not needed with Worlds) "
Allocator commitToWorld: world
[ 
  self unassignedVars: (world at: #unassignedVars).
  spilledVars := (world at: #spilledVars).
  variables keys do: 
    [:varN | (variables at: varN) assigned: ((world at: #Variables) at: varN) ].
  banks do: [:bank | bank allocations: ((world at: #RegBanks) at: bank) ].
  ^true
]

Allocator newVariable: aName class: aClass liveRangeFrom: aRangeStart to: aRangeEnd
[ 
    | var | 
    var := Variable new.    
    var name: aName length: (classToLengthMap at: aClass) 
	category: (classToCategoryMap at: aClass).
    var addLiveRangeFrom: aRangeStart to: aRangeEnd.
    variables at: aName put: var.
    self addVariable: var.
    Variable addInstance: var.
    ^var
]

Allocator addVariable: var
[
    | idx |
    " keep unassignedVars sorted by start live intervals "
    idx := 0.
    [ unassignedVars size > idx and: 
      [ var liveRanges first first > 
        ( unassignedVars at: idx ) liveRanges first first ] ] whileTrue: 
          [ idx := idx + 1 ].
    unassignedVars insert: var atIndex: idx.
]

Allocator var: varN addUsedInstruction: instIdx
[
    ( variables at: varN ) addUsedInstruction: instIdx
]

Allocator var: varN addFixedInstruction: instIdx
[
    ( variables at: varN ) addFixedInstruction: instIdx
]

Variable name: aName length: aLength category: aCategory
[ 
  number := aName.
  name := #V , aName.
  length := aLength.
  category := aCategory.
  liveRanges := OrderedCollection new.
  usedAtInsts := OrderedCollection new.
  fixedAtInsts := OrderedCollection new.
  assignedRegs := IdentityDictionary new.
  assigned := false
]

Variable addLiveRangeFrom: aRangeStart to: aRangeEnd
[
  ( aRangeEnd \\ 2 = 0 ) ifFalse: [ aRangeEnd := aRangeEnd + 1 ]. 
  ( liveRanges size > 0 and: [ aRangeStart = liveRanges last second ] )
     ifTrue: [ ( liveRanges at: ( liveRanges size - 1 ) ) at: 1 put: aRangeEnd ]
    ifFalse: [ liveRanges add: (Array with: aRangeStart with: aRangeEnd) ]
]

Variable cutLiveRangesAndSelfDeallocateForSpillAt: instIdx
[
    | i e newLiveRanges dealocRanges |
    i := 0.
    newLiveRanges := OrderedCollection new.
    dealocRanges := OrderedCollection new.
    liveRanges do: [:lRange | 
      e := self firstFixedAtInstsFrom: instIdx withinInterval: lRange.
      e ifFalse: [ e := lRange second ]. 
      ( lRange second < instIdx or: [ lRange first > e ] ) 
      ifTrue: [ newLiveRanges add: lRange ]
     ifFalse: [ ( instIdx > lRange first )
                  ifTrue: [ newLiveRanges add: ( Array with: lRange first with: instIdx ) ].
                ( lRange second > e ) 
                   ifTrue: [ newLiveRanges add: ( Array with: e with: lRange second ).
                             dealocRanges add: ( Array with: instIdx with: e ) ]
                  ifFalse: [ dealocRanges add: ( Array with: instIdx with: lRange second ) ].
                ( i < ( liveRanges size - 1 ) )
                  ifTrue: [ instIdx := (liveRanges at: (i + 1)) first ] ].
      i := i + 1 ].
    liveRanges := newLiveRanges.
    'var: ' put. self print. ' new liveRange: ' put.  liveRanges println.
    'var: ' put. self print. ' dealocate: ' put. dealocRanges println.
    assignedRegs keys do: 
      [:regN | ( assignedRegs at: regN ) deallocateIntervals: dealocRanges  ].
]

Variable firstFixedAtInstsFrom: instIdx
[   
    fixedAtInsts do: [:idx | idx >= instIdx ifTrue: [ ^idx ] ].
    ^false
]

Variable firstFixedAtInstsFrom: instIdx withinInterval: intv
[   | s e |
    s := ( intv first ) max: instIdx.
    e := intv second.
    instIdx > e ifTrue: [ ^false ].
    fixedAtInsts do: [:idx | ( idx >= s and: [ idx <= e ] )  ifTrue: [ ^idx ] ].
    ^false
]


Variable addUsedInstruction: instIdx
[
    self addFixedInstruction: instIdx.
    usedAtInsts add: instIdx
]

Variable addFixedInstruction: instIdx
[
    ( instIdx == ( liveRanges first first + 2 ) or: 
      [ instIdx == ( liveRanges last second - 2 ) ] )
      ifTrue: [ ^false ].
    fixedAtInsts add: instIdx.
    ^true
]

Array covers: idx
[
    ^( idx >= self first asInstIdxStart and: [ idx <= self second ] )
]

Variable nextUsedInstructionAfter: instIdx withinIntervals: intvs
[
    intvs do: 
      [:intv | usedAtInsts do: 
        [:iIdx | ( iIdx >= instIdx and: [ intv covers: iIdx ] ) ifTrue: [ ^iIdx ] ] ].
    ^false
]

Allocator liveVariablesAt: instIdx
[    | res |
     res := OrderedCollection new.
     variables keys do: 
       [:varN | | var s e | 
	 var := variables at: varN.
         ( spilledVars includesKey: varN ) ifFalse: 
           [ s := var liveRanges first first.
            e := var liveRanges last second.
           ( s < instIdx and: [ e > instIdx ] ) ifTrue: [ res add: varN ] ] ].
     ^res 
]

Allocator findVarToSpillAt: instIdx checkLiveIntervals: intvs
[   | pickedVarN bestIdx | 
    bestIdx := 0.
    ( self liveVariablesAt: instIdx ) do: 
      [:varN | | var idx |
               var := variables at: varN.
               idx := var nextUsedInstructionAfter: instIdx withinIntervals: intvs.
               idx ifFalse: [ ^varN ].
               idx ifTrue: [ idx > bestIdx ifTrue: [ bestIdx := idx.
	                                             pickedVarN := varN ] ] ].
    ^pickedVarN
]


Variable length [ ^length ]
Variable number [ ^number ]
Variable category [ ^category ]
Variable isAssigned [ ^assigned ]
Variable assigned: isAssigned [ assigned := isAssigned ]
Variable usedAtInsts [ ^usedAtInsts ]
Variable fixedAtInsts [ ^fixedAtInsts ]
Variable liveRanges [ ^liveRanges ]
Variable assignedRegs [ ^assignedRegs ]
Variable removeFirstLiveRange [ liveRanges := liveRanges copyFrom: 1 ]

Allocator newRegBank: aName category: aCategory section: aSection index: aIndex
[   | bank |
    bank := RegBank new.
    bank name: aName category: aCategory section: aSection index: aIndex.
    bank allocations: (Array new: programSize * 2).
    banksDic at: aName put: bank.
    banks add: bank.
    RegBank addInstance: bank.
    ^bank
]

Allocator newRegister: aName length: aLength category: aCategory number: aNumber 
          banks: regBankNames
[   | reg numBanks regBanks |
    reg := Register new.
    numBanks := regBankNames size.
    regBanks := Array new: numBanks.
    0 to: ( numBanks - 1 ) do: 
      [:n | regBanks at: n put: ( banksDic at: ( regBankNames at: n ) ) ].
    reg name: aName length: aLength category: aCategory number: aNumber banks: regBanks.
    registers at: aNumber put: reg.
    Register addInstance: reg.
    ^reg
]

Register name: aName length: aLength category: aCategory number: aNumber banks: regBanks
[
  name := aName.
  category := aCategory.
  length := aLength.
  banks := regBanks.
  number := aNumber.
]

RegBank name: aName category: aCategory section: aSection index: aIndex 
[
  name := aName.
  category := aCategory.
  section := aSection.
  index := aIndex
]

RegBank hasAllocationAtIdx: idx 
[   | alloc | 
    alloc := allocations at: idx. 
    ^( alloc and: [ alloc ~= #precolored ] )
]

RegBank allocations: allcs [ allocations := Array withAll: allcs ]
RegBank freeAtIdx: idx [ ^( allocations at: idx ) not ]
RegBank allocations [ ^allocations ]
RegBank index [ ^index ]
RegBank section [ ^section ]
RegBank category [ ^category ]

Register banks [ ^banks ]
Register length [ ^length ]
Register category [ ^category ]
Register number [ ^number ]

Allocator run
[ | solutionWorld |

  'Before:' putln.
  self draw. 
  solutionWorld := John forObject: self 
		      satisfyGoal: #allocation 
	              withActions: (Array with: #assign:var:allRanges: with: #split:to:)
                            options: #(Debug).
  solutionWorld ifTrue: [ self commitToWorld: solutionWorld ].
  'After:' putln.
  self draw.
]

" Main Program "

" Allocator passes its current World, JOHN returns the solution World, 
  which Allocator can commit to "


[ | Al V1024 V1025 V1026 V1027 V1028 V1029 |
Al := Allocator newWithProgramSize: 22. 
Al precolor: 1 intervalStart: 22 intervalEnd: 30. 
Al precolor: 1 intervalStart: 50 intervalEnd: 58. 
Al precolor: 1 intervalStart: 74 intervalEnd: 82. 
Al precolor: 2 intervalStart: 22 intervalEnd: 30. 
Al precolor: 2 intervalStart: 50 intervalEnd: 58. 
Al precolor: 2 intervalStart: 74 intervalEnd: 82. 
Al precolor: 3 intervalStart: 22 intervalEnd: 30. 
Al precolor: 3 intervalStart: 50 intervalEnd: 58. 
Al precolor: 3 intervalStart: 74 intervalEnd: 82. 
Al precolor: 9 intervalStart: 22 intervalEnd: 23. 
Al precolor: 9 intervalStart: 50 intervalEnd: 51. 
Al precolor: 9 intervalStart: 74 intervalEnd: 75. 
Al precolor: 10 intervalStart: 22 intervalEnd: 23. 
Al precolor: 10 intervalStart: 50 intervalEnd: 51. 
Al precolor: 10 intervalStart: 74 intervalEnd: 75. 
Al precolor: 11 intervalStart: 22 intervalEnd: 23. 
Al precolor: 11 intervalStart: 50 intervalEnd: 51. 
Al precolor: 11 intervalStart: 74 intervalEnd: 75. 
Al precolor: 12 intervalStart: 22 intervalEnd: 23. 
Al precolor: 12 intervalStart: 50 intervalEnd: 51. 
Al precolor: 12 intervalStart: 74 intervalEnd: 75. 
Al precolor: 15 intervalStart: 22 intervalEnd: 23. 
Al precolor: 15 intervalStart: 50 intervalEnd: 51. 
Al precolor: 15 intervalStart: 74 intervalEnd: 75. 
Al precolor: 16 intervalStart: 22 intervalEnd: 23. 
Al precolor: 16 intervalStart: 50 intervalEnd: 51. 
Al precolor: 16 intervalStart: 74 intervalEnd: 75. 
Al precolor: 17 intervalStart: 22 intervalEnd: 30. 
Al precolor: 17 intervalStart: 50 intervalEnd: 58. 
Al precolor: 17 intervalStart: 74 intervalEnd: 82. 
Al precolor: 20 intervalStart: 22 intervalEnd: 23. 
Al precolor: 20 intervalStart: 50 intervalEnd: 51. 
Al precolor: 20 intervalStart: 74 intervalEnd: 75. 
Al precolor: 22 intervalStart: 22 intervalEnd: 23. 
Al precolor: 22 intervalStart: 50 intervalEnd: 51. 
Al precolor: 22 intervalStart: 74 intervalEnd: 75. 
Al precolor: 27 intervalStart: 22 intervalEnd: 23. 
Al precolor: 27 intervalStart: 50 intervalEnd: 51. 
Al precolor: 27 intervalStart: 74 intervalEnd: 75. 
Al precolor: 28 intervalStart: 22 intervalEnd: 23. 
Al precolor: 28 intervalStart: 50 intervalEnd: 51. 
Al precolor: 28 intervalStart: 74 intervalEnd: 75. 
Al precolor: 29 intervalStart: 22 intervalEnd: 23. 
Al precolor: 29 intervalStart: 50 intervalEnd: 51. 
Al precolor: 29 intervalStart: 74 intervalEnd: 75. 
Al precolor: 30 intervalStart: 22 intervalEnd: 23. 
Al precolor: 30 intervalStart: 50 intervalEnd: 51. 
Al precolor: 30 intervalStart: 74 intervalEnd: 75. 
Al precolor: 31 intervalStart: 22 intervalEnd: 23. 
Al precolor: 31 intervalStart: 50 intervalEnd: 51. 
Al precolor: 31 intervalStart: 74 intervalEnd: 75. 
Al precolor: 32 intervalStart: 22 intervalEnd: 23. 
Al precolor: 32 intervalStart: 50 intervalEnd: 51. 
Al precolor: 32 intervalStart: 74 intervalEnd: 75. 
Al precolor: 33 intervalStart: 22 intervalEnd: 23. 
Al precolor: 33 intervalStart: 50 intervalEnd: 51. 
Al precolor: 33 intervalStart: 74 intervalEnd: 75. 
Al precolor: 35 intervalStart: 22 intervalEnd: 23. 
Al precolor: 35 intervalStart: 50 intervalEnd: 51. 
Al precolor: 35 intervalStart: 74 intervalEnd: 75. 
Al precolor: 36 intervalStart: 22 intervalEnd: 23. 
Al precolor: 36 intervalStart: 50 intervalEnd: 51. 
Al precolor: 36 intervalStart: 74 intervalEnd: 75. 
Al precolor: 37 intervalStart: 22 intervalEnd: 23. 
Al precolor: 37 intervalStart: 50 intervalEnd: 51. 
Al precolor: 37 intervalStart: 74 intervalEnd: 75. 
Al precolor: 38 intervalStart: 22 intervalEnd: 23. 
Al precolor: 38 intervalStart: 50 intervalEnd: 51. 
Al precolor: 38 intervalStart: 74 intervalEnd: 75. 
Al precolor: 39 intervalStart: 22 intervalEnd: 23. 
Al precolor: 39 intervalStart: 50 intervalEnd: 51. 
Al precolor: 39 intervalStart: 74 intervalEnd: 75. 
Al precolor: 40 intervalStart: 22 intervalEnd: 23. 
Al precolor: 40 intervalStart: 50 intervalEnd: 51. 
Al precolor: 40 intervalStart: 74 intervalEnd: 75. 
Al precolor: 41 intervalStart: 22 intervalEnd: 23. 
Al precolor: 41 intervalStart: 50 intervalEnd: 51. 
Al precolor: 41 intervalStart: 74 intervalEnd: 75. 
Al precolor: 42 intervalStart: 22 intervalEnd: 23. 
Al precolor: 42 intervalStart: 50 intervalEnd: 51. 
Al precolor: 42 intervalStart: 74 intervalEnd: 75. 
Al precolor: 96 intervalStart: 22 intervalEnd: 23. 
Al precolor: 96 intervalStart: 50 intervalEnd: 51. 
Al precolor: 96 intervalStart: 74 intervalEnd: 75. 
Al precolor: 97 intervalStart: 22 intervalEnd: 23. 
Al precolor: 97 intervalStart: 50 intervalEnd: 51. 
Al precolor: 97 intervalStart: 74 intervalEnd: 75. 
Al precolor: 104 intervalStart: 22 intervalEnd: 23. 
Al precolor: 104 intervalStart: 50 intervalEnd: 51. 
Al precolor: 104 intervalStart: 74 intervalEnd: 75. 
Al precolor: 105 intervalStart: 22 intervalEnd: 23. 
Al precolor: 105 intervalStart: 50 intervalEnd: 51. 
Al precolor: 105 intervalStart: 74 intervalEnd: 75. 
Al precolor: 106 intervalStart: 22 intervalEnd: 23. 
Al precolor: 106 intervalStart: 50 intervalEnd: 51. 
Al precolor: 106 intervalStart: 74 intervalEnd: 75. 
Al precolor: 107 intervalStart: 22 intervalEnd: 23. 
Al precolor: 107 intervalStart: 50 intervalEnd: 51. 
Al precolor: 107 intervalStart: 74 intervalEnd: 75. 
Al precolor: 108 intervalStart: 22 intervalEnd: 23. 
Al precolor: 108 intervalStart: 50 intervalEnd: 51. 
Al precolor: 108 intervalStart: 74 intervalEnd: 75. 
V1024 := Al newVariable: 1024 class: 2 liveRangeFrom: 6 to: 10. 
V1025 := Al newVariable: 1025 class: 2 liveRangeFrom: 10 to: 14. 
V1025 addLiveRangeFrom: 14 to: 38. 
V1026 := Al newVariable: 1026 class: 6 liveRangeFrom: 30 to: 66. 
V1027 := Al newVariable: 1027 class: 3 liveRangeFrom: 38 to: 42. 
V1028 := Al newVariable: 1028 class: 6 liveRangeFrom: 58 to: 59. 
V1029 := Al newVariable: 1029 class: 6 liveRangeFrom: 82 to: 83. 
Al var: 1024 addUsedInstruction: 4. 
Al var: 1025 addUsedInstruction: 8. 
Al var: 1024 addUsedInstruction: 8. 
Al var: 1024 addFixedInstruction: 8. 
Al var: 1025 addUsedInstruction: 12. 
Al var: 1025 addUsedInstruction: 12. 
Al var: 1025 addFixedInstruction: 12. 
Al var: 1025 addUsedInstruction: 16. 
Al var: 1025 addFixedInstruction: 16. 
Al var: 1026 addUsedInstruction: 28. 
Al var: 1027 addUsedInstruction: 36. 
Al var: 1025 addUsedInstruction: 36. 
Al var: 1025 addFixedInstruction: 36. 
Al var: 1027 addUsedInstruction: 40. 
Al var: 1027 addFixedInstruction: 40. 
Al var: 1028 addUsedInstruction: 56. 
Al var: 1026 addUsedInstruction: 64. 
Al var: 1026 addFixedInstruction: 64. 
Al var: 1029 addUsedInstruction: 80. 
    Al run.
]


"
[ | Al V1024 V1025 V1026 V1027 V1028 V1029 V1030 V1031 V1032 V1033 V1034 V1035 V1036 V1037 V1038 V1039 V1040 V1041 V1042 V1043 V1044 V1045 V1046 V1047 V1048 V1049 V1050 V1051 V1052 V1053 V1054 V1055 V1056 V1057 V1058 V1059 V1060 V1061 V1062 V1063 V1064 V1065 V1066 V1067 V1068 V1069 V1070 V1071 V1072 V1073 V1074 V1075 V1076 V1077 V1078 V1079 V1080 V1081 V1082 V1083 V1084 V1085 V1086 V1087 V1088 V1089 V1090 V1091 V1092 V1093 V1094 V1095 |
Al := Allocator newWithProgramSize: 74. 
V1024 := Al newVariable: 1024 class: 6 liveRangeFrom: 18 to: 280. 
V1024 addLiveRangeFrom: 288 to: 292. 
V1025 := Al newVariable: 1025 class: 6 liveRangeFrom: 2 to: 280. 
V1025 addLiveRangeFrom: 288 to: 292. 
V1026 := Al newVariable: 1026 class: 6 liveRangeFrom: 6 to: 38. 
V1027 := Al newVariable: 1027 class: 6 liveRangeFrom: 10 to: 280. 
V1027 addLiveRangeFrom: 288 to: 292. 
V1028 := Al newVariable: 1028 class: 6 liveRangeFrom: 14 to: 280. 
V1028 addLiveRangeFrom: 288 to: 292. 
V1029 := Al newVariable: 1029 class: 6 liveRangeFrom: 38 to: 42. 
V1029 addLiveRangeFrom: 42 to: 280. 
V1029 addLiveRangeFrom: 288 to: 292. 
V1030 := Al newVariable: 1030 class: 6 liveRangeFrom: 30 to: 280. 
V1030 addLiveRangeFrom: 288 to: 292. 
V1031 := Al newVariable: 1031 class: 6 liveRangeFrom: 34 to: 280. 
V1031 addLiveRangeFrom: 288 to: 292. 
V1032 := Al newVariable: 1032 class: 6 liveRangeFrom: 62 to: 234. 
V1032 addLiveRangeFrom: 288 to: 292. 
V1033 := Al newVariable: 1033 class: 6 liveRangeFrom: 66 to: 242. 
V1033 addLiveRangeFrom: 288 to: 292. 
V1034 := Al newVariable: 1034 class: 6 liveRangeFrom: 70 to: 250. 
V1034 addLiveRangeFrom: 288 to: 292. 
V1035 := Al newVariable: 1035 class: 6 liveRangeFrom: 86 to: 90. 
V1035 addLiveRangeFrom: 90 to: 228. 
V1036 := Al newVariable: 1036 class: 6 liveRangeFrom: 106 to: 228. 
V1037 := Al newVariable: 1037 class: 6 liveRangeFrom: 102 to: 228. 
V1038 := Al newVariable: 1038 class: 6 liveRangeFrom: 126 to: 182. 
V1039 := Al newVariable: 1039 class: 6 liveRangeFrom: 130 to: 190. 
V1040 := Al newVariable: 1040 class: 6 liveRangeFrom: 134 to: 198. 
V1041 := Al newVariable: 1041 class: 6 liveRangeFrom: 198 to: 202. 
V1041 addLiveRangeFrom: 202 to: 228. 
V1042 := Al newVariable: 1042 class: 6 liveRangeFrom: 190 to: 194. 
V1042 addLiveRangeFrom: 194 to: 228. 
V1043 := Al newVariable: 1043 class: 6 liveRangeFrom: 182 to: 186. 
V1043 addLiveRangeFrom: 186 to: 228. 
V1044 := Al newVariable: 1044 class: 6 liveRangeFrom: 250 to: 254. 
V1044 addLiveRangeFrom: 254 to: 280. 
V1045 := Al newVariable: 1045 class: 6 liveRangeFrom: 242 to: 246. 
V1045 addLiveRangeFrom: 246 to: 280. 
V1046 := Al newVariable: 1046 class: 6 liveRangeFrom: 234 to: 238. 
V1046 addLiveRangeFrom: 238 to: 280. 
V1049 := Al newVariable: 1049 class: 2 liveRangeFrom: 150 to: 170. 
V1050 := Al newVariable: 1050 class: 2 liveRangeFrom: 154 to: 178. 
V1051 := Al newVariable: 1051 class: 2 liveRangeFrom: 158 to: 174. 
V1052 := Al newVariable: 1052 class: 2 liveRangeFrom: 162 to: 166. 
V1054 := Al newVariable: 1054 class: 6 liveRangeFrom: 50 to: 60. 
V1057 := Al newVariable: 1057 class: 6 liveRangeFrom: 54 to: 60. 
V1060 := Al newVariable: 1060 class: 6 liveRangeFrom: 46 to: 60. 
V1063 := Al newVariable: 1063 class: 6 liveRangeFrom: 114 to: 124. 
V1066 := Al newVariable: 1066 class: 6 liveRangeFrom: 118 to: 124. 
V1069 := Al newVariable: 1069 class: 6 liveRangeFrom: 110 to: 124. 
Al var: 1025 addUsedInstruction: 0. 
Al var: 1026 addUsedInstruction: 4. 
Al var: 1027 addUsedInstruction: 8. 
Al var: 1028 addUsedInstruction: 12. 
Al var: 1024 addUsedInstruction: 16. 
Al var: 1026 addUsedInstruction: 20. 
Al var: 1030 addUsedInstruction: 28. 
Al var: 1027 addUsedInstruction: 28. 
Al var: 1031 addUsedInstruction: 32. 
Al var: 1028 addUsedInstruction: 32. 
Al var: 1029 addUsedInstruction: 36. 
Al var: 1026 addUsedInstruction: 36. 
Al var: 1029 addUsedInstruction: 40. 
Al var: 1029 addUsedInstruction: 40. 
Al var: 1060 addUsedInstruction: 44. 
Al var: 1054 addUsedInstruction: 48. 
Al var: 1031 addUsedInstruction: 48. 
Al var: 1057 addUsedInstruction: 52. 
Al var: 1030 addUsedInstruction: 52. 
Al var: 1032 addUsedInstruction: 60. 
Al var: 1054 addUsedInstruction: 60. 
Al var: 1046 addUsedInstruction: 60. 
Al var: 1033 addUsedInstruction: 64. 
Al var: 1057 addUsedInstruction: 64. 
Al var: 1045 addUsedInstruction: 64. 
Al var: 1034 addUsedInstruction: 68. 
Al var: 1060 addUsedInstruction: 68. 
Al var: 1044 addUsedInstruction: 68. 
Al var: 1035 addUsedInstruction: 84. 
Al var: 1034 addUsedInstruction: 84. 
Al var: 1035 addUsedInstruction: 88. 
Al var: 1035 addUsedInstruction: 88. 
Al var: 1035 addUsedInstruction: 92. 
Al var: 1037 addUsedInstruction: 100. 
Al var: 1028 addUsedInstruction: 100. 
Al var: 1036 addUsedInstruction: 104. 
Al var: 1027 addUsedInstruction: 104. 
Al var: 1069 addUsedInstruction: 108. 
Al var: 1063 addUsedInstruction: 112. 
Al var: 1033 addUsedInstruction: 112. 
Al var: 1066 addUsedInstruction: 116. 
Al var: 1032 addUsedInstruction: 116. 
Al var: 1038 addUsedInstruction: 124. 
Al var: 1063 addUsedInstruction: 124. 
Al var: 1043 addUsedInstruction: 124. 
Al var: 1039 addUsedInstruction: 128. 
Al var: 1066 addUsedInstruction: 128. 
Al var: 1042 addUsedInstruction: 128. 
Al var: 1040 addUsedInstruction: 132. 
Al var: 1069 addUsedInstruction: 132. 
Al var: 1041 addUsedInstruction: 132. 
Al var: 1049 addUsedInstruction: 148. 
Al var: 1025 addUsedInstruction: 148. 
Al var: 1038 addUsedInstruction: 148. 
Al var: 1050 addUsedInstruction: 152. 
Al var: 1025 addUsedInstruction: 152. 
Al var: 1039 addUsedInstruction: 152. 
Al var: 1051 addUsedInstruction: 156. 
Al var: 1024 addUsedInstruction: 156. 
Al var: 1039 addUsedInstruction: 156. 
Al var: 1052 addUsedInstruction: 160. 
Al var: 1024 addUsedInstruction: 160. 
Al var: 1038 addUsedInstruction: 160. 
Al var: 1024 addUsedInstruction: 164. 
Al var: 1039 addUsedInstruction: 164. 
Al var: 1052 addUsedInstruction: 164. 
Al var: 1025 addUsedInstruction: 168. 
Al var: 1039 addUsedInstruction: 168. 
Al var: 1049 addUsedInstruction: 168. 
Al var: 1024 addUsedInstruction: 172. 
Al var: 1038 addUsedInstruction: 172. 
Al var: 1051 addUsedInstruction: 172. 
Al var: 1025 addUsedInstruction: 176. 
Al var: 1038 addUsedInstruction: 176. 
Al var: 1050 addUsedInstruction: 176. 
Al var: 1043 addUsedInstruction: 180. 
Al var: 1038 addUsedInstruction: 180. 
Al var: 1043 addUsedInstruction: 184. 
Al var: 1043 addUsedInstruction: 184. 
Al var: 1037 addUsedInstruction: 184. 
Al var: 1042 addUsedInstruction: 188. 
Al var: 1039 addUsedInstruction: 188. 
Al var: 1042 addUsedInstruction: 192. 
Al var: 1042 addUsedInstruction: 192. 
Al var: 1036 addUsedInstruction: 192. 
Al var: 1041 addUsedInstruction: 196. 
Al var: 1040 addUsedInstruction: 196. 
Al var: 1041 addUsedInstruction: 200. 
Al var: 1041 addUsedInstruction: 200. 
Al var: 1041 addUsedInstruction: 204. 
Al var: 1035 addUsedInstruction: 204. 
Al var: 1046 addUsedInstruction: 232. 
Al var: 1032 addUsedInstruction: 232. 
Al var: 1046 addUsedInstruction: 236. 
Al var: 1046 addUsedInstruction: 236. 
Al var: 1031 addUsedInstruction: 236. 
Al var: 1045 addUsedInstruction: 240. 
Al var: 1033 addUsedInstruction: 240. 
Al var: 1045 addUsedInstruction: 244. 
Al var: 1045 addUsedInstruction: 244. 
Al var: 1030 addUsedInstruction: 244. 
Al var: 1044 addUsedInstruction: 248. 
Al var: 1034 addUsedInstruction: 248. 
Al var: 1044 addUsedInstruction: 252. 
Al var: 1044 addUsedInstruction: 252. 
Al var: 1044 addUsedInstruction: 256. 
Al var: 1029 addUsedInstruction: 256. 
Al run.
]
"

" Sample Output: 

"
