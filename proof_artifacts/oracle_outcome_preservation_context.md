# Oracle Context: Outcome-Aware Structured Preservation

Mode: critique / repair theorem architecture. I need a Lean proof strategy that avoids proof-only fusion cases.

Repository: `/Users/dan/Projects/evm-compiler`

Build command: `/Users/dan/.elan/bin/lake build`

Current state:
- Lean build is green.
- Proof-hole grep over `EvmCompiler` is clean.
- Active goal is not complete because the refactored structured layer still has an explicit `AssemblyReplay` certificate boundary.

Relevant public objective:
Prove outcome-aware preservation for structured `if`, `switch`, `break`/`continue`, and loops; derive replay from successful source runs; compose with labeled assembly -> EVM theorem; keep gas/PC/jump/outside-world assumptions explicit.

Current syntax:
```lean
inductive Mode where
  | regular | brk | cont

structure Outcome where
  state : EVMState
  mode : Mode

inductive Stmt where
  | code (code : Code)
  | if_ (cond : Code) (body : Block)
  | switch (scrutinee : Code) (cases : List (Word × Block))
      (defaultBody : Option Block)
  | for_ (init : Block) (cond : Code) (post : Block) (body : Block)
  | brk
  | cont
```

Current compiler shape:
```lean
structure CompileContext where
  breakLabel? : Option Assembly.Label := none
  continueLabel? : Option Assembly.Label := none

def Stmt.jumpOrInvalid : Option Assembly.Label → Assembly.Program
  | some label => [Assembly.Instr.jump label]
  | none => [Assembly.Instr.prim .invalid]

def Stmt.switchTestCode (value : Word) : Code :=
  [BasicInstr.op .dup1, BasicInstr.push value, BasicInstr.op .eq]

def Stmt.switchTest (base : LabelSupply) (idx : Nat) (value : Word) :
    Assembly.Program :=
  (switchTestCode value).toAssembly ++
    [Assembly.Instr.jumpi (LabelSupply.label base (idx + 2))]

def Stmt.switchTests (base : LabelSupply) : Nat → List (Word × Block) →
    Assembly.Program
  | _idx, [] => []
  | idx, (value, _body) :: rest =>
      switchTest base idx value ++ switchTests base (idx + 1) rest
```

Switch compile body:
```lean
| .switch scrutinee cases defaultBody =>
    let endLabel := LabelSupply.label supply 0
    let defaultLabel := LabelSupply.label supply 1
    let compiledCases :=
      SwitchCases.compileFromCtx cases ctx endLabel supply
        (LabelSupply.next supply) 0
    let compiledDefault :=
      SwitchDefault.compileFromCtx defaultBody ctx endLabel defaultLabel
        compiledCases.next
    { code :=
        scrutinee.toAssembly ++
          Stmt.switchTests supply 0 cases ++
          [Assembly.Instr.jump defaultLabel] ++
          compiledCases.code ++
          compiledDefault.code ++
          [Assembly.Instr.label endLabel]
      next := compiledDefault.next }
```

Case/default compile:
```lean
def SwitchCases.compileFromCtx
    (cases : List (Word × Block)) (ctx : CompileContext)
    (endLabel : Assembly.Label) (base supply : LabelSupply) (idx : Nat) :
    CompileResult :=
  match cases with
  | [] => { code := [], next := supply }
  | (_value, body) :: rest =>
      let caseLabel := LabelSupply.label base (idx + 2)
      let compiledBody := Block.compileFromCtx body ctx supply
      let compiledHead : CompileResult :=
        { code :=
            [ Assembly.Instr.label caseLabel
            , Assembly.Instr.prim .pop
            ] ++
            compiledBody.code ++
            [Assembly.Instr.jump endLabel]
          next := compiledBody.next }
      let compiledTail :=
        SwitchCases.compileFromCtx rest ctx endLabel base compiledHead.next
          (idx + 1)
      compiledHead.append compiledTail

def SwitchDefault.compileFromCtx
    (defaultBody : Option Block) (ctx : CompileContext)
    (endLabel defaultLabel : Assembly.Label) (supply : LabelSupply) :
    CompileResult :=
  match defaultBody with
  | none =>
      { code :=
          [ Assembly.Instr.label defaultLabel
          , Assembly.Instr.prim .pop
          , Assembly.Instr.jump endLabel
          ]
        next := supply }
  | some body =>
      let compiledBody := Block.compileFromCtx body ctx supply
      { code :=
          [ Assembly.Instr.label defaultLabel
          , Assembly.Instr.prim .pop
          ] ++
          compiledBody.code ++
          [Assembly.Instr.jump endLabel]
        next := compiledBody.next }
```

Current preservation contract:
```lean
def ContextResolves (ctx : CompileContext) (program : Assembly.Program) : Prop :=
  (∀ label, ctx.breakLabel? = some label →
    ∃ dest, Assembly.Program.labelPc program label = some dest) ∧
  (∀ label, ctx.continueLabel? = some label →
    ∃ dest, Assembly.Program.labelPc program label = some dest)

def OutcomeRel (ctx : CompileContext) (program : Assembly.Program)
    (regularPc : Word) (outcome : Outcome) (target : EVMState) : Prop :=
  match outcome.mode with
  | .regular => RelAt regularPc target outcome.state
  | .brk =>
      ∃ label dest,
        ctx.breakLabel? = some label ∧
          Assembly.Program.labelPc program label = some dest ∧
            RelAt (EvmYul.UInt256.ofNat dest) target outcome.state
  | .cont =>
      ∃ label dest,
        ctx.continueLabel? = some label ∧
          Assembly.Program.labelPc program label = some dest ∧
            RelAt (EvmYul.UInt256.ofNat dest) target outcome.state

def BlockPreservesCtx (ctx : CompileContext) (supply : LabelSupply)
    (block : Block) : Prop :=
  ∀ {pre post : Assembly.Program} {fuel : Nat}
    {source target : EVMState} {outcome : Outcome},
    AssemblyProgram.labelsLt supply pre →
    Block.WF ctx.breakLabel?.isSome ctx.continueLabel?.isSome block →
    ContextResolves ctx
      (pre ++ (Block.compileFromCtx block ctx supply).code ++ post) →
    AssemblyProgram.PCFitsFrom pre
      (Block.compileFromCtx block ctx supply).code →
    RelAt (Assembly.Program.pcAfter pre) target source →
    Block.Eval fuel block source outcome →
    ARun
      (pre ++ (Block.compileFromCtx block ctx supply).code ++ post)
      target
      (fun target' =>
        OutcomeRel ctx
          (pre ++ (Block.compileFromCtx block ctx supply).code ++ post)
          (Assembly.Program.pcAfter
            (pre ++ (Block.compileFromCtx block ctx supply).code))
          outcome target')
```

Already proved:
- `StmtPreservesCtx.code`
- `StmtPreservesCtx.brk`
- `StmtPreservesCtx.cont`
- `StmtPreservesCtx.if_`
- `BlockPreservesCtx.nil`
- `BlockPreservesCtx.cons`
- `Switch.switchTestCode_runCondition` for the real compiler helper:
  from `state.stack.pop = some (stack, scrutinee)` it gives
  `Code.runCondition (Stmt.switchTestCode value) state =
    .ok (state', decide (value = scrutinee))`
  and `eraseControl state' = eraseControl state`.

Problem:
Need to add `StmtPreservesCtx.switch` and `StmtPreservesCtx.for_` without making a giant brittle proof or introducing proof-only mirrors of compiler output. In particular, switch dispatch should be proven compositionally over `Stmt.switchTests` and `SwitchCases.compileFromCtx`, not as a hand-fused proof of one whole switch layout.

Question:
What are the right helper theorem statements for:
1. running generated switch tests to either a case label or default jump;
2. entering a case/default body and handling regular vs break/continue outcomes;
3. proving `for_` with `break`/`continue` outcomes using `OutcomeRel` and `ContextResolves`;
so that the final `CompilerPreservation.block` recursor and `assemblyReplayOfRun` are clean?

Please be concrete about theorem statement shapes and induction variables. Avoid invented Lean library names. I’m not asking for a full file-sized proof, but for a proof architecture that will check without dispatcher blowup or proof-side code duplication.
