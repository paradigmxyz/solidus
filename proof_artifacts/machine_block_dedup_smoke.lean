import EvmCompiler.Assembly.MachineBlockDedupSimulation

open EvmCompiler

namespace MachineBlockDedupSmoke

def entry : Assembly.Label := .named "entry"
def canonical : Assembly.Label := .named "canonical"
def duplicate : Assembly.Label := .named "duplicate"
def bridge : Assembly.Label := .named "bridge"

def source : Assembly.Program :=
  [ .label entry
  , .jump canonical
  , .label canonical
  , .prim .stop
  , .label bridge
  , .jump duplicate
  , .label duplicate
  , .prim .stop
  ]

def expected : Assembly.Program :=
  [ .label entry
  , .jump canonical
  , .label canonical
  , .prim .stop
  , .label bridge
  , .jump canonical
  ]

def fixedExpected : Assembly.Program :=
  [ .label entry
  , .jump canonical
  , .label canonical
  , .prim .stop
  ]

#guard Assembly.MachineBlockDedup.check entry source
  (Assembly.MachineBlockDedup.candidate entry source)

#guard (Assembly.MachineBlockDedup.candidate entry source).output.accepted

#guard Assembly.MachineBlockDedup.fixedPointCheck entry source
  (Assembly.MachineBlockDedup.fixedPointCandidate entry source)

#guard decide (
  (Assembly.MachineBlockDedup.fixedPointCandidate entry source).output =
    fixedExpected)

#guard
  (Assembly.MachineBlockDedup.fixedPointCandidate entry source).rounds.length =
    2

example :
    (Assembly.MachineBlockDedup.candidate entry source).output = expected := by
  rfl

def openPredecessor : Assembly.Label := .named "open-predecessor"

def unsafeFallthroughSource : Assembly.Program :=
  [ .label entry
  , .prim .stop
  , .label openPredecessor
  , .push (EvmYul.UInt256.ofNat 1)
  , .label duplicate
  , .prim .stop
  ]

#guard !Assembly.MachineBlockDedup.check entry unsafeFallthroughSource
  (Assembly.MachineBlockDedup.candidate entry unsafeFallthroughSource)

#guard decide (
  Assembly.MachineBlockDedup.fixedPointOptimize entry unsafeFallthroughSource =
    unsafeFallthroughSource)

def positionDependentSource : Assembly.Program :=
  [ .label entry
  , .prim .pc
  , .prim .stop
  ]

#guard !Assembly.MachineBlockDedup.check entry positionDependentSource
  (Assembly.MachineBlockDedup.candidate entry positionDependentSource)

def pushed : Assembly.Label := .named "pushed"

def pushLabelSource : Assembly.Program :=
  [ .label entry
  , .pushLabel pushed
  , .prim .stop
  , .label pushed
  , .prim .stop
  ]

#guard !Assembly.MachineBlockDedup.check entry pushLabelSource
  (Assembly.MachineBlockDedup.candidate entry pushLabelSource)

def dynamicJumpSource : Assembly.Program :=
  [ .label entry
  , .jumpDynamic
  , .prim .stop
  ]

#guard !Assembly.MachineBlockDedup.check entry dynamicJumpSource
  (Assembly.MachineBlockDedup.candidate entry dynamicJumpSource)

#print axioms Assembly.MachineBlockDedup.exact_code_correspondence_of_check
#print axioms Assembly.MachineBlockDedup.output_Accepted_of_check
#print axioms Assembly.MachineBlockDedup.optimize_accepted
#print axioms Assembly.MachineBlockDedup.CertifiedTrace.lift
#print axioms Assembly.MachineBlockDedup.fixedPointOptimize_accepted
#print axioms Assembly.MachineBlockDedup.fixedPointOptimize_entryRunResultRel
#print axioms
  Assembly.MachineBlockDedup.fixedPointOptimize_entryRunResultRel_of_stepSemantics
#print axioms
  Assembly.MachineBlockDedup.checkedRoundStepSemantics
#print axioms
  Assembly.MachineBlockDedup.fixedPointOptimize_entryRunResultRel_unconditional

end MachineBlockDedupSmoke
