# Oracle Request: Discharging Structured Procedure Layout Certificate

We are in a Lean 4 project `/Users/dan/Projects/evm-compiler`.

Goal: finish a procedure-aware `Structured` control layer compiling to labeled
EVM assembly. The current public theorem is too weak because it takes:

```lean
theorem compile_preserves
    {program : Program} {sourceFuel : Nat} {initial : EVMState}
    {sourceOutcome : Outcome}
    (certificate : ProcedurePreservation.CompilationCertificate program)
    (hAccepted : Program.Accepted program)
    (hInitialPc : initial.pc = Assembly.Program.pcAfter [])
    (hSource : program.run sourceFuel initial = .ok sourceOutcome) :
    ∃ targetFuel targetOutcome,
      Assembly.Source.runNResult program.compile targetFuel initial =
        .ok targetOutcome ∧
      WholeProgramOutcomeRel sourceOutcome targetOutcome
```

The user wants the public certificate assumption discharged, except for truly
fundamental resource assumptions such as PC/no-wrap if needed.

The current `CompilationCertificate` is:

```lean
structure CompilationCertificate (program : Program) where
  layout : ProgramLayout program
  asm_eq : layout.asm = program.compile
  sites_eq : layout.sites = CompiledProgram.allCalls program
  mainFits : AssemblyProgram.PCFitsFrom [] (CompiledProgram.main program).code
```

But the real problem is that `ProgramLayout` is not pure layout. It includes
semantic preservation facts for every procedure body:

```lean
structure CallLayout (program : Program) (asm : Assembly.Program)
    (sites : List CallSite) where
  noDupTokens : (sites.map CallSite.token).Nodup
  procBodySupply :
    ∀ {name : Name} {proc : Proc},
      ProcList.lookup? name program.procs = some proc → LabelSupply
  procDispatchSupply :
    ∀ {name : Name} {proc : Proc},
      ProcList.lookup? name program.procs = some proc → LabelSupply
  procSegment :
    ∀ {name : Name} {proc : Proc}
      (hLookup : ProcList.lookup? name program.procs = some proc),
      CodeSegment asm
        (procSegment program proc (procBodySupply hLookup)
          (procDispatchSupply hLookup) sites)
  procPreserves :
    ∀ {name : Name} {proc : Proc}
      (hLookup : ProcList.lookup? name program.procs = some proc),
      BlockPreserves program (bodyCtx program proc)
        (procBodySupply hLookup) proc.body

structure ProcLayout (program : Program) (asm : Assembly.Program)
    (sites : List CallSite) (proc : Proc) where
  bodySupply : LabelSupply
  dispatchSupply : LabelSupply
  segment :
    CodeSegment asm
      (procSegment program proc bodySupply dispatchSupply sites)
  preserves :
    BlockPreserves program (bodyCtx program proc) bodySupply proc.body

structure ProgramLayout (program : Program) where
  asm : Assembly.Program
  sites : List CallSite
  exactLabels : ExactLabels asm
  noDupTokens : (sites.map CallSite.token).Nodup
  tokenNoDupForProc :
    ∀ proc : Proc,
      ((sites.filter (CallSite.forProc proc.name)).map CallSite.token).Nodup
  procLayout :
    ∀ {name : Name} {proc : Proc},
      ProcList.lookup? name program.procs = some proc →
        ProcLayout program asm sites proc
```

Source semantics is fuel-indexed. In `Stmt.Eval.call_*`, a call at fuel+1 runs
callee body at fuel:

```lean
| call_regular {fuel : Nat} {name : Name} {state : RunState}
    {proc : Proc} {args callerStack stack : EvmYul.Stack Word}
    {bodyState returned : RunState} {frame : ReturnDest}
    (hLookup : ProcList.lookup? name program.procs = some proc)
    (hSplit : StackFrame.splitArgs? proc.argc state.evm.stack =
      some (args, callerStack))
    (hBody : Block.Eval program fuel proc.body
      ((state.withEVM { state.evm with stack := args }).pushReturn
        callerStack proc.retc)
      (Outcome.regular bodyState))
    (hPop : bodyState.popReturn? = some (frame, returned))
    (hAttach :
      StackFrame.attachReturns? frame bodyState.evm.stack = some stack) :
    Stmt.Eval program (fuel + 1) (.call name) state
      (Outcome.regular
        (returned.withEVM { bodyState.evm with stack := stack }))
```

Existing syntax-recursive preservation theorem:

```lean
namespace CompilerPreservationProgramLayout

mutual
  theorem block {program : Program} {layout : ProgramLayout program}
      {ctx : CompileContext} {supply : LabelSupply} {block : Block}
      {canBreak canContinue canLeave : Bool}
      (hWF : Block.WF canBreak canContinue canLeave block)
      (hRunner : Block.RunnerSafe block)
      (hFrame : Block.FrameSafe block)
      (hTerminal : Block.TerminalSafe block)
      (hCtx : ControlContextSupports canBreak canContinue canLeave ctx) :
      BlockPreservesInProgramLayout layout ctx supply block := ...

  theorem stmt ... :
      StmtPreservesInProgramLayout layout ctx supply stmt := by
    ...
    | call =>
        exact ProcedurePreservation.preserves_call_in_programLayout layout
end

theorem main_block ...
```

This works only because `layout` already contains `procPreserves`. That is the
assumption to eliminate.

Relevant constraints:

- no new axioms/sorries/unsafe/partial;
- do not hide compiler-generated semantic evidence inside `Accepted`;
- pure layout evidence such as label resolution/token uniqueness should be
separated from semantic procedure-body preservation;
- recursive procedures should remain supported;
- source call semantics decreases fuel, so a fuel-indexed induction should be
available;
- existing non-call structured proofs are large and checked under
`ProgramLayout`, e.g. `preserves_if_in_programLayout`,
`preserves_switch_in_programLayout`, `preserves_for_in_programLayout`, but they
take full `BlockPreservesInProgramLayout` premises for sub-bodies.

Question: What is the cleanest Lean architecture to discharge this certificate
without rewriting the entire switch/for proof stack? In particular, can we:

1. split `ProgramLayout` into pure layout and a separate semantic call oracle;
2. prove the semantic call oracle by fuel induction over source evals;
3. preserve reuse of existing `preserves_*_in_programLayout` theorems without
   creating circular proof terms; or
4. is a new eval-indexed preservation family unavoidable?

Please give a concrete theorem/predicate shape and a minimal refactor sequence
that will pass Lean termination and avoid proof blowup.
