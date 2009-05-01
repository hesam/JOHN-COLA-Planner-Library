{ import: Object }
{ import: PepsiPrimitivesModel }

"
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;											     ;;;
;;; JOHN - Implements an automated planner and constraint handler program as a COLA library  ;;;
;;;											     ;;;
;;;        Allows COLA objects to solve their problems using the underlying reasoning/solver ;;;
;;;        engine. Objects can describe a problem as a planning problem, by providing the    ;;;
;;;        solver the name of methods which represent the goal, actions for the object that  ;;;
;;;        represent a step in the direction of satisfying the goal, along with a copy of    ;;;
;;;        the current World the object is in.                                               ;;;
;;;											     ;;;
;;;        JOHN will take this World and reason about it to find a solution World in which   ;;;
;;;        the goal is satisfied (if one exists), then passes the solution World (or false)  ;;;
;;;        back to the object. If the object wishes to, it commits to the solution World.    ;;;
;;;											     ;;;
;;;        goal methods may have an optimization method which dynamically specify            ;;;
;;;	   the actions that should be explored to reach the goal 			     ;;;
;;;	   action methods must be attached to a method returning the types of its arguments. ;;;
;;;	   action methods may also have an optimization method which dynamically impose	     ;;;
;;;        constraints on its arguments to specify which argument values should be explored  ;;;
;;;                                                               			     ;;;
;;;        Optimizations have the effect of pruning the search tree.                         ;;;
;;;        Heuristics (not supported yet) have the effect of re-ordering search tree nodes.  ;;;
;;;                                                               			     ;;;
;;;                                                               			     ;;;
;;;        * Future inference method:                           			     ;;;
;;;                                                               			     ;;;
;;;        JOHN will solve the problem by encoding the problem into logical relations, then  ;;;
;;;        into a Satisfiability problem instance, solves it using MiniSat solver, then      ;;;
;;;        decodes the solution back for the calling object                                  ;;;
;;;                                                               			     ;;;
;;;        * Current inference method: - brute force DFID search if no heuristics defined    ;;;
;;;                                    - IDA* search when heuristics defined                 ;;;
;;;                                                               			     ;;;
;;;                                                               			     ;;;
;;; Author:        Hesam Samimi                                   			     ;;;
;;;                                                               			     ;;;
;;; Revision:      # 1.0                                      			             ;;;
;;; Last Update:   03-23-2009								     ;;; 
;;;                                                               			     ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;          
;;; Module: John
;;;
;;; Input: Problem description (goal and action method names), 
;;;        along with a copy of object's current World.
;;;        - method representing a goal may have an optimization method named: 
;;;          #<goalMethodName>_optimizaiton attached to it (to dynamically specify
;;;          actions to explore)
;;;        - methods representing an action must have a method named: 
;;;          #<actionMethodName>_argTypes to return the types of its argument in an array
;;;          (the types can be either class names or explicit arrays of possible values)
;;;        - methods representing an action may also have optimization methods named:
;;;          #<actionMethodName>_optimization attached to them (to dynamically
;;;          enforce constraints on the argument values for the method)
;;;        
;;; Output: Solution World if goal is satisfiable, false otherwise.
;;;
;;; Methods: 
;;;
;;;  <return: solution world / false> := 
;;;     John forObject: <obj> 
;;;        satisfyGoal: <method name associated with goal (returns true/false)>
;;;        withActions: <method names associated with actions 
;;;                      (makes a change in object -- a step in satisfying the goal)> 
;;;
;;;  Example:
;;;    solutionWorld := John forObject: Puzzle satisfyGoal: #colored 
                              withActions: #(paintNextPiece:)
;;;    solutionWorld ifTrue: [ Puzzle commitToWorld: solutionWorld ].
;;;

"

John : Object (learnings goalWorldHash)

" Globals/Options "
johnGlobals := [ | glb opt |
                   opt := IdentityDictionary new. 
		   opt at: #Debug put: false. 
                   opt at: #Learn put: false.
                   opt at: #UseLearnings put: false.
                   glb := IdentityDictionary new. 
                   glb at: #opts put: opt.
                   glb at: #timer put: Date new.
                   glb at: #startTime put: 0.
                   glb ]

" 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;			                   Planner					     ;;;
;;;                                                                                          ;;;
;;;                  satisfy a goal of the object by search based inference                  ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
"
John new: anObj goal: goal
[
    self := John new.
    (self opt: #Learn) 
       ifTrue: [ learnings := IdentityDictionary new ]
      ifFalse: [ (self opt: #UseLearnings) 
                   ifTrue: [ self loadLearningsForObj: anObj goal: goal ] ]
]

John forObject: anObj satisfyGoal: goal withActions: actions options: opts
[
    self setOpts: opts.
    ^self forObject: anObj satisfyGoal: goal withActions: actions
]

John forObject: anObj satisfyGoal: goal withActions: actions
[
    | possActionArgVals currWorld solutionWorld heuristicMtd heuristicMtdBy th |
    "is it already satisfied:"
    currWorld := anObj worldSnapshot.
    (anObj perform: goal) ifTrue: [ ^currWorld ].
    self := John new: anObj goal: goal.
    "if goal has optimizations, cannot determine the list of possible actions statically:"    
    possActionArgVals := (anObj understands: (goal , #_optimization))
      ifTrue: [ false ] 
     ifFalse: [ self forObject: anObj getPossibleArgValuesForActions: actions ].
    " check if heuristic function defined for this goal, if yes use IDA* search / if not DFID "
    (self opt: #UseLearnings) ifTrue: [ heuristicMtd := #_heuristicFromLearnings:. heuristicMtdBy := self ] 
                      ifFalse: [ heuristicMtd := goal , #_heuristic. heuristicMtdBy := anObj ].
    (heuristicMtdBy understands: heuristicMtd) ifTrue: [
         th := heuristicMtdBy perform: heuristicMtd withArguments: (Array with: currWorld).
         solutionWorld := self doIDAStarSearchThreshold: th
			       world: currWorld object: anObj goal: goal actions: actions 
	                       possActionArgVals: possActionArgVals 
	                       scoreWorlds: (Array with: heuristicMtdBy with: heuristicMtd) ]
      ifFalse: [
         (self opt: #Learn) ifTrue: [ self learnForObj: anObj goal: goal world: currWorld score: 0 ].
         solutionWorld := self doDFIDSearchDepth: 1 
	                       worlds: (OrderedCollection with: currWorld) 
                               object: anObj goal: goal actions: actions 
	                       possActionArgVals: possActionArgVals ].
    (self opt: #Debug) ifTrue: 
      [ | solutionTime units opts |
	solutionTime := (johnGlobals at: #startTime) - (johnGlobals at: #timer) initialize seconds. 
	solutionTime > 0 ifTrue:
          [ units := ' sec ]'.
	    solutionTime > 60 ifTrue: [ units := ' min ]'. solutionTime := solutionTime / 60. ]. 
	    '[ solution time: ' put. solutionTime print. units putln. '' putln ] ].
    (self opt: #Learn) ifTrue: [ self recordLearningsForObj: anObj goal: goal ].
    ^solutionWorld
]

John perform: expression byObject: anObj inWorld: world
[
      | currWorld res |
      currWorld := anObj worldSnapshot.
      anObj commitToWorld: world.  
      res := anObj perform: expression.
      anObj commitToWorld: currWorld.  
      ^res
]

John doDFIDSearchDepth: depth worlds: worlds object: anObj goal: goal 
     actions: actions possActionArgVals: possActionArgVals
[
    | nextPWs nextPWsAndGoalEval debug |
    debug := self opt: #Debug.
    debug ifTrue: [ 'at depth ' put. depth print. ' ...' put. ].
    nextPWsAndGoalEval := self getNextPossibleWorldsFor: worlds depth: depth 
			       object: anObj goal: goal 
	                       actions: actions possActionArgVals: possActionArgVals
	                       scoreWorlds: false learn: (self opt: #Learn).
    nextPWs := nextPWsAndGoalEval second.
    (nextPWsAndGoalEval first) ifTrue: [ debug ifTrue: [ '' putln. '' putln ].
                                         ^nextPWs ].
    debug ifTrue: [ ' # possible worlds: ' put. nextPWs size println ].
    ^(nextPWs isEmpty 
          ifTrue: [ false ] 
         ifFalse: [ self doDFIDSearchDepth: (depth + 1) worlds: nextPWs object: anObj goal: goal 
                         actions: actions possActionArgVals: possActionArgVals ])
]

John doIDAStarSearchThreshold: th world: world object: anObj goal: goal actions: actions 
     possActionArgVals: possActionArgVals scoreWorlds: heuristicMtd
[   | itr debug |
    debug := self opt: #Debug.
    [ true ] whileTrue: 
      [ debug ifTrue: [ 'at threshold ' put. th print. ' ...' putln ].
        itr := self doIDAStarSearchThreshold: th cost: 0 world: world object: anObj 
	            goal: goal actions: actions possActionArgVals: possActionArgVals 
                    scoreWorlds: heuristicMtd.
        itr first ifTrue: [ ^itr second ] 
                 ifFalse: [ th := itr second ] ]
]

John doIDAStarSearchThreshold: th cost: c world: world object: anObj goal: goal 
     actions: actions possActionArgVals: possActionArgVals scoreWorlds: heuristicMtd
[   | nextPWs nextPWsAndGoalEval currWorld nextTh | 

    nextPWsAndGoalEval := self getNextPossibleWorldsFor: (Array with: world) depth: th
			       object: anObj goal: goal actions: actions 
                               possActionArgVals: possActionArgVals scoreWorlds: heuristicMtd learn: (self opt: #Learn).
    nextPWs := nextPWsAndGoalEval second.
    (nextPWsAndGoalEval first) ifTrue: [ ^(Array with: true with: nextPWs) ].
    nextPWs isEmpty ifTrue: [ ^(Array with: false with: false) ].
    currWorld := anObj worldSnapshot.
    nextPWs do: [:pwWithScore |  | score pw checkChild | 
	score := pwWithScore first + c + 1.
        score <= th ifTrue: 
          [ pw := pwWithScore second.
	    anObj commitToWorld: pw.
            checkChild := self doIDAStarSearchThreshold: th cost: (c + 1) world: pw 
			       object: anObj goal: goal actions: actions 
			       possActionArgVals: possActionArgVals scoreWorlds: heuristicMtd.
            anObj commitToWorld: currWorld.
	    checkChild first 
               ifTrue: [ ^(Array with: true with: checkChild second) ]
               ifFalse: [ score := checkChild second ] ].
        (nextTh not or: [ score < nextTh ]) ifTrue: [ nextTh := score ] ].
    ^(Array with: false with: nextTh)
]

John getNextPossibleWorldsFor: worlds depth: depth object: anObj goal: goal actions: actions 
     possActionArgVals: possActionArgVals scoreWorlds: heuristicMtd learn: learn
[
    | pws currWorldOrig currWorld wld action possArgVals res heuristicScore |
    pws := OrderedCollection new.
    currWorldOrig := anObj worldSnapshot.
    worlds do: 
      [:world | 
	 anObj commitToWorld: world.
	 currWorld := anObj worldSnapshot.
         possActionArgVals ifFalse:
           [ possActionArgVals := self forObject: anObj goal: goal 
		   		       getPossibleArgValuesForActionsByOptimizations: actions ].
	 possActionArgVals do:
           [:actionAndArgCombos | | argCombos optMtd |
	      action := actionAndArgCombos first.              
	      possArgVals := actionAndArgCombos second.
              optMtd := action , #_optimization:.
              argCombos := (anObj understands: optMtd)
                ifTrue: [ possArgVals crossProductSelect: 
                            [:args | anObj perform: optMtd withArguments: args ] ] 
                ifFalse: [ possArgVals crossProduct ].
              argCombos do:
                [:args | 
                  " if action has optimizations filter the tried args here..."
                    (anObj perform: action withArguments: args) 
		      ifTrue: [ wld := anObj worldSnapshot.
		                res := anObj perform: goal.
                                learn ifTrue: 
                                  [ self learnForObj: anObj goal: goal world: wld score: depth ].
                                res ifTrue: [ anObj commitToWorld: currWorldOrig.
                                              ^(Array with: true with: wld) ]
	                           ifFalse: [ heuristicMtd 
                                                ifTrue: [ heuristicScore := (heuristicMtd first)
					  	              perform: (heuristicMtd second)
						              withArguments: (Array with: wld).
                                                          pws add: (Array with: heuristicScore 
						                           with: wld) ]
				               ifFalse: [ pws add: wld ] ].
			        anObj commitToWorld: currWorld ] ] ] ].
    anObj commitToWorld: currWorldOrig.  
    ^(Array with: false with: pws)
]

John forObject: anObj goal: goal getPossibleArgValuesForActionsByOptimizations: actions 
[   | limitedActions |
    limitedActions := (anObj understands: (goal , #_optimization)) 
                         ifTrue: [ anObj perform: (goal , #_optimization) ]
                        ifFalse: [ actions ].
    ^self forObject: anObj getPossibleArgValuesForActions: limitedActions 
]

John forObject: anObj getPossibleArgValuesForActions: actions
[   | possActionArgVals argTypes possParams action  |
    possActionArgVals := Array new: (actions size).
    0 to: (actions size - 1) do: 
      [:i | action := actions at: i.
	    argTypes := (anObj understands: (action , #_argTypes:)) 
		  	   ifTrue: [ anObj perform: (action , #_argTypes:) ]
                          ifFalse: [ Array with: (Array with: nil) ].
            possParams := Array new: (argTypes size).
            0 to: (argTypes size - 1) do: [:x | | t | 
                                              t := argTypes at: x.
				              possParams at: x put: 
				                ((t isArray) ifTrue: [ t ] 
			                                       ifFalse: [ t instances ]) ].
            possActionArgVals at: i put: (Array with: action with: possParams) ].
    ^possActionArgVals
]

John learnForObj: anObj goal: goal world: wld score: heurValue
[ | hash |
    hash := wld worldHash.
    (learnings includesKey: hash) ifFalse: [ learnings at: hash put: heurValue ]
]

John recordLearningsForObj: anObj goal: goal
[ | fh |
    fh := File create: '/tmp/John.' , anObj name , '.' , goal , '.learnings'.
    learnings saveTo: fh.
    fh close
]

John loadLearningsForObj: anObj goal: goal
[ | fh |
    learnings := IdentityDictionary new.
    fh := File open: '/tmp/John.' , anObj name , '.' , goal , '.learnings'.
    learnings loadFrom: (fh contents asString readStream).
    fh close.
    goalWorldHash := (anObj perform: (goal , #_worldSnapshot)) worldHash
]

John _heuristicFromLearnings: world
[
    ^((learnings at: goalWorldHash) - (learnings at: (world worldHash))) abs
]

John setOpts: opts 
[ | johnOpts |
    johnOpts := johnGlobals at: #opts.
    opts do: [:opt | johnOpts at: opt put: true.
                     opt = #Debug ifTrue: 
                       [ johnGlobals at: #startTime 
                                 put: (johnGlobals at: #timer) initialize seconds ] ]
]

John opt: opt [ ^(johnGlobals at: #opts) at: opt ]

" 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;			                   ObjectPlus					     ;;;
;;;                                                                                          ;;;
;;;                   keeps track of instanciated objects for each type, and more...         ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
"

ObjectPlus : Object (name type instances dependents selfDependent constraints constraintVars)

"fixme"
ObjectPlus new
[
    self := super new.
    constraints := IdentityDictionary new.
    constraintVars := IdentityDictionary new.
    dependents := IdentityDictionary new.
]

ObjectPlus new: aName type: aType
[   
    self := self new.
    type := aType.
    name := aName.
    aType addInstance: self
]

ObjectPlus new: aType [ ^self new: #noName type: aType ]
ObjectPlus addInstance: obj [ instances add: obj ]
ObjectPlus type: aType [ type := aType ]
ObjectPlus name: aName [ name := aName ]
ObjectPlus type: aType name: aName [ type := aType. name := aName ]
ObjectPlus name [ ^name ]
ObjectPlus type [ ^type ]
ObjectPlus instances [ ^instances ]
ObjectPlus asString [ ^self name asString ]
ObjectPlus print [ self name asString put ]
ObjectPlus setNil: var [ self assign: var value: nil ]
ObjectPlus println [ self print. '' putln ]
" to be defined by the inheriting object: "
ObjectPlus worldSnapshot [ ^true ]
ObjectPlus commitToWorld: world [ ^true ]
"ObjectPlus returnFalse [ ^false ]
 ObjectPlus doesNotUnderstand: aSelector [ ^self _bind: #returnFalse ]"

ObjectPlus inits 
[ 
    instances := OrderedCollection new. 
    constraints := IdentityDictionary new.
    constraintVars := IdentityDictionary new
]

ObjectPlus assign: var value: val
[ 
    self perform: (var , (':' asSymbol)) withArguments: (Array with: val) 
]

UndefinedObject hash [ ^#nil hash ] 
_object hash [ ^#true hash ]
ObjectPlus hash [ ^name hash ]

IdentityDictionary worldHash
[   | hash val |
    hash := #h.
    self do: [:assoc | val := assoc value.
                       hash := hash , val hash ].
    ^hash
]

"
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;			              Constraint Handler   				     ;;;
;;;                                                                                          ;;;
;;;                 wrapper around assignments to handle object's constraints:               ;;;
;;;                applies unit resolutions when possible and detects conflicts              ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
"

Constraint : Object (name dependency)

Constraint new: aName dependency: vars 
[
    self := Constraint new.
    name := aName.
    dependency := vars
]

Constraint name [ ^name ]
Constraint dependency [ ^dependency ]


Constraint otherVars: var
[ | res |
    res := OrderedCollection new.
    dependency do: [:v | v = var ifFalse: [ res add: v  ] ].
    ^res
]

John forObj: anObj assign: var value: val
[ | origWorld deps consts moreUnitResol conflDtctr conflict |
    origWorld := anObj constraintWorldSnapshot.
    anObj assign: var value: val.

    " a) constraints for dependent objects: "
    deps := anObj dependentsOn: var.
    "anObj print. ' ' put. var print. ' dependents:' put. deps println."
    deps ifTrue: [
      deps do: [:assoc | | dObj | 
                 dObj := assoc key.
                 consts := assoc value. 
                 "dObj println.  consts println. "
                  consts do: [:con | 
                    dObj perform: (con , #_constraint:) with: anObj ]
                   ] ].
    " b) self constraints: "
    anObj isSelfDependent ifTrue: [
      conflDtctr := IdentityDictionary new.
      conflDtctr at: (anObj constraintWorldSnapshot worldHash) put: true.
      consts := anObj constraints keys.
      moreUnitResol := true.
      [ moreUnitResol ] whileTrue: 
        [ | unitResolDone res |
          moreUnitResol := false.
	  consts do: [:con |
            res := anObj unitResolution: con var: var conflDetector: conflDtctr.
            res first ifTrue: [ moreUnitResol := true ].
            conflict := res second.
            (conflict or: [ (anObj constraint: con) not ])
              ifTrue: [ con print. ' violated!' putln. 
                        anObj commitToConstraintWorld: origWorld.
	                ^false ] ] ] ].
    ^true
]

ObjectPlus constraints [ ^(type classConstraints) merged: constraints ]
ObjectPlus constraintVars [ ^(type classConstraintVars) merged: constraintVars ]
ObjectPlus classConstraints [ ^constraints ]
ObjectPlus classConstraintVars [ ^constraintVars ]
ObjectPlus selfDependent [ ^selfDependent ]
ObjectPlus isSelfDependent [ ^type selfDependent or: [ selfDependent ] ]
ObjectPlus dependents [ ^dependents ]

ObjectPlus subscribeDependencyTo: anObj on: aVar constraint: constId 
[ 
    anObj addDependent: self on: aVar constraint: constId
]

ObjectPlus addDependent: anObj on: aVar constraint: constId
[ | d |
    (dependents includesKey: aVar) ifFalse: [ dependents at: aVar put: IdentityDictionary new ].
    d := dependents at: aVar.
    (d includesKey: anObj) ifFalse: [ d at: anObj put: OrderedCollection new ].
    (d at: anObj) add: constId
]

ObjectPlus dependentsOn: var  
[ 
    ^(dependents includesKey: var) ifTrue: [ dependents at: var ] ifFalse: [ nil ]
]

ObjectPlus addConstraint: constId selfOnly: isSelfConst
[ 
    ^self addConstraint: constId selfOnly: isSelfConst dependency: #() 
]

ObjectPlus addConstraint: constId selfOnly: isSelfConst dependency: dependency
[ | const |
    " if this is a class constraint: "
    isSelfConst ifTrue: [ selfDependent := true ].
    const := Constraint new: constId dependency: dependency.
    isSelfConst ifTrue: [ dependency do: [:v | constraintVars at: v put: true ] ]
              ifFalse: [ dependency do: [:v | self subscribeDependencyTo: v first on: v second 
	                                           constraint: constId ] ].
    constraints at: constId put: const
]

ObjectPlus nonNilVarVals: constId
[ | res |
    res := OrderedCollection new.
    (self constraintVars: constId) do: 
      [:val | val ifTrue: [ res add: val ] ].
    ^res
]

ObjectPlus anyNilVars: constId
[ 
    (self constraintVars: constId) do: 
      [:val | val ifFalse: [ ^true ] ].
    ^false
]

ObjectPlus exactlyOneNilVar: constId
[ | c | 
    c := 0.
    (self constraintVars: constId) do: 
      [:val | val ifNil: [ c := c + 1. c > 1 ifTrue: [ ^false ] ] ].
    ^(c == 1)
]


ObjectPlus unitResolution: constId var: var conflDetector: conflDtctr
[ | mtd wldHash |
    mtd := constId , #_unitResolution:.
    ^((self understands: mtd) and: [ self unitResolutionTest: constId var: var ])
        ifTrue: [ (self perform: mtd with: var)
		    ifTrue: [ wldHash := self constraintWorldSnapshot worldHash.
		              (conflDtctr includesKey: wldHash)
                                 ifTrue: [ Array with: true with: true ]
		                ifFalse: [ conflDtctr at: wldHash put: true.
	                                   Array with: true with: false ] ]
                   ifFalse: [ ^Array with: false with: false ] ]
       ifFalse: [ Array with: false with: false ]
]

ObjectPlus unitResolutionTest: constId var: var
[ | const |
    const := self constraints at: constId. 
    (self exactlyOneNilVar: constId) ifTrue: [ ^true ].
    (self constraint: constId) ifFalse: 
      [ (const otherVars: var) do: [:other | self setNil: other ]. 
        ^(self exactlyOneNilVar: constId) ].
    ^false
]

ObjectPlus constraint: constId
[
    (self anyNilVars: constId) ifTrue: [ ^true ].
    ^(self perform: (constId , #_constraint))
]

ObjectPlus constraintVars: constId
[
    ^(self perform: (constId , #_vars))
]

ObjectPlus constraintWorldSnapshot
[ | wld |
    wld := IdentityDictionary new.  
    self constraintVars keys do: [:v | wld at: v put: (self perform: v) ].
    ^wld
]

ObjectPlus commitToConstraintWorld: wld
[ 
    self constraintVars keys do: [:v | self assign: v value: (wld at: v) ].
    ^true
]
