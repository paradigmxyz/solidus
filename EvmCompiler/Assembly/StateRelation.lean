import EvmCompiler.Assembly.Syntax
import EvmYul.EVM.State
import EvmYul.EVM.StateOps

namespace EvmCompiler
namespace Assembly

abbrev EVMState := EvmYul.EVM.State

def eraseGas (state : EVMState) : EVMState :=
  { state with
    gasAvailable := EvmYul.UInt256.ofNat 0
    execLength := 0
  }

def eraseControl (state : EVMState) : EVMState :=
  { eraseGas state with pc := EvmYul.UInt256.ofNat 0 }

def SameData (target source : EVMState) : Prop :=
  eraseControl target = eraseControl source

/--
Erase only compiler-owned control counters while retaining all runtime data,
including available gas.
-/
def eraseRuntimeControl (state : EVMState) : EVMState :=
  { state with
    pc := EvmYul.UInt256.ofNat 0
    execLength := 0 }

def SameRuntimeData (target source : EVMState) : Prop :=
  eraseRuntimeControl target = eraseRuntimeControl source

namespace SameRuntimeData

theorem refl (state : EVMState) :
    SameRuntimeData state state := rfl

theorem symm {target source : EVMState}
    (hRel : SameRuntimeData target source) :
    SameRuntimeData source target :=
  Eq.symm hRel

theorem trans {first second third : EVMState}
    (hFirst : SameRuntimeData first second)
    (hSecond : SameRuntimeData second third) :
    SameRuntimeData first third :=
  Eq.trans hFirst hSecond

theorem sameData {target source : EVMState}
    (hRel : SameRuntimeData target source) :
    SameData target source := by
  cases target
  cases source
  simp [SameRuntimeData, eraseRuntimeControl, SameData,
    eraseControl, eraseGas] at hRel ⊢
  constructor
  · simpa [hRel.1]
  · exact hRel.2

theorem stack_eq {target source : EVMState}
    (hRel : SameRuntimeData target source) :
    target.stack = source.stack := by
  cases target
  cases source
  simp [SameRuntimeData, eraseRuntimeControl] at hRel
  exact hRel.2

theorem with_pc_left {target source : EVMState} (pc : Word)
    (hRel : SameRuntimeData target source) :
    SameRuntimeData { target with pc := pc } source := by
  cases target
  cases source
  simpa [SameRuntimeData, eraseRuntimeControl] using hRel

theorem with_pc_right {target source : EVMState} (pc : Word)
    (hRel : SameRuntimeData target source) :
    SameRuntimeData target { source with pc := pc } := by
  exact symm (with_pc_left pc hRel.symm)

theorem incrPC_left {target source : EVMState}
    (hRel : SameRuntimeData target source) :
    SameRuntimeData target.incrPC source := by
  cases target
  cases source
  simpa [SameRuntimeData, eraseRuntimeControl,
    EvmYul.EVM.State.incrPC] using hRel

theorem incrPC_right {target source : EVMState}
    (hRel : SameRuntimeData target source) :
    SameRuntimeData target source.incrPC := by
  exact symm (incrPC_left hRel.symm)

theorem replaceStackAndIncrPC
    {target source : EVMState}
    {targetStack sourceStack : EvmYul.Stack Word} {pcΔ : Nat}
    (hRel : SameRuntimeData target source)
    (hStack : targetStack = sourceStack) :
    SameRuntimeData
      (target.replaceStackAndIncrPC targetStack (pcΔ := pcΔ))
      (source.replaceStackAndIncrPC sourceStack (pcΔ := pcΔ)) := by
  cases target
  cases source
  simp [SameRuntimeData, eraseRuntimeControl] at hRel ⊢
  exact ⟨hRel.1, hStack⟩

theorem replaceStack
    {target source : EVMState}
    {targetStack sourceStack : EvmYul.Stack Word}
    (hRel : SameRuntimeData target source)
    (hStack : targetStack = sourceStack) :
    SameRuntimeData
      { target with stack := targetStack }
      { source with stack := sourceStack } := by
  cases target
  cases source
  simp [SameRuntimeData, eraseRuntimeControl] at hRel ⊢
  exact ⟨hRel.1, hStack⟩

end SameRuntimeData

theorem eraseControl_with_pc (state : EVMState) (pc : Word) :
    eraseControl { state with pc := pc } = eraseControl state := by
  cases state
  rfl

theorem eraseControl_with_stack (state : EVMState)
    (stack : EvmYul.Stack Word) :
    eraseControl { state with stack := stack } =
      { eraseControl state with stack := stack } := by
  cases state
  rfl

theorem eraseControl_with_stack_congr {left right : EVMState}
    {stack : EvmYul.Stack Word}
    (hEq : eraseControl left = eraseControl right) :
    eraseControl { left with stack := stack } =
      eraseControl { right with stack := stack } := by
  cases left
  cases right
  simp [eraseControl, eraseGas] at hEq ⊢
  exact hEq.1

theorem eraseRuntimeControl_with_stack (state : EVMState)
    (stack : EvmYul.Stack Word) :
    eraseRuntimeControl { state with stack := stack } =
      { eraseRuntimeControl state with stack := stack } := by
  cases state
  rfl

theorem eraseRuntimeControl_with_stack_congr {left right : EVMState}
    {stack : EvmYul.Stack Word}
    (hEq : eraseRuntimeControl left = eraseRuntimeControl right) :
    eraseRuntimeControl { left with stack := stack } =
      eraseRuntimeControl { right with stack := stack } := by
  cases left
  cases right
  simp [eraseRuntimeControl] at hEq ⊢
  exact hEq.1

theorem eraseControl_replaceStackAndIncrPC_of_eq
    {left right : EVMState}
    {leftStack rightStack : EvmYul.Stack Word} {pcΔ : Nat}
    (hEq : eraseControl left = eraseControl right)
    (hStack : leftStack = rightStack) :
    eraseControl
        (left.replaceStackAndIncrPC leftStack (pcΔ := pcΔ)) =
      eraseControl
        (right.replaceStackAndIncrPC rightStack (pcΔ := pcΔ)) := by
  cases left
  cases right
  simp [eraseControl, eraseGas] at hEq ⊢
  exact ⟨hEq.1, hStack⟩

theorem SameData.refl (state : EVMState) :
    SameData state state := rfl

theorem SameData.trans {first second third : EVMState}
    (hFirst : SameData first second)
    (hSecond : SameData second third) :
    SameData first third :=
  Eq.trans hFirst hSecond

end Assembly
end EvmCompiler
