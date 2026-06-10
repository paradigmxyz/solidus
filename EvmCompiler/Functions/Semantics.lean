import EvmCompiler.Functions.LoweringCore
import EvmCompiler.Locals.Semantics

namespace EvmCompiler
namespace Functions

abbrev Outcome := Locals.Outcome
abbrev RunState := Locals.RunState
abbrev Ctx := Locals.Ctx

namespace Switch

def select (scrutinee : Word) :
    List (Word × Block) → Option Block → Option Block
  | [], defaultBody => defaultBody
  | (value, body) :: rest, defaultBody =>
      if value = scrutinee then
        some body
      else
        select scrutinee rest defaultBody

end Switch

namespace Direct

def zero : Word :=
  EvmYul.UInt256.ofNat 0

def evalArgs (ctx : Ctx) : List (Expr 1) → RunState →
    Except EVMException RunState
  | [], state => .ok state
  | arg :: rest, state => do
      let evm ←
        Locals.Direct.Expr.ExprSeq.runCode ctx 0
          (Lower.argExprs (arg :: rest)) state.evm
      .ok (state.withEVM evm)

def pushReturns (ctx : Ctx) : List Name → RunState →
    Except EVMException RunState
  | [], state => .ok state
  | name :: rest, state => do
      let evm ←
        Locals.Direct.Expr.ExprSeq.runCode ctx 0
          (Lower.returnExprs (name :: rest)) state.evm
      .ok (state.withEVM evm)

def initReturns : List Name → Ctx → RunState →
    Except EVMException (RunState × Ctx)
  | [], ctx, state => .ok (state, ctx)
  | name :: rest, ctx, state => do
      let state' ← Locals.Direct.Expr.runState ctx (.lit zero) state
      initReturns rest (ctx.withLayout (name :: ctx.layout)) state'

def assignTop (ctx : Ctx) (name : Name) (state : RunState) :
    Except EVMException RunState := do
  let depth ← (Locals.Layout.lookupDepth? name ctx.layout).elim
    Structured.invalid pure
  let swapOp ← (Locals.StackOp.swap? depth).elim Structured.invalid pure
  let evmAfterSwap ← swapOp.step state.evm
  let evmAfterPop ← Structured.BasicOp.pop.step evmAfterSwap
  .ok (state.withEVM evmAfterPop)

def assignTopWithOffset (ctx : Ctx) (offset : Nat) (name : Name)
    (state : RunState) :
    Except EVMException RunState := do
  let depth ← (Locals.Layout.lookupDepth? name ctx.layout).elim
    Structured.invalid pure
  let swapOp ← (Locals.StackOp.swap? (offset + depth)).elim
    Structured.invalid pure
  let evmAfterSwap ← swapOp.step state.evm
  let evmAfterPop ← Structured.BasicOp.pop.step evmAfterSwap
  .ok (state.withEVM evmAfterPop)

def assignReturnedTops (ctx : Ctx) : List Name → RunState →
    Except EVMException RunState
  | [], state => .ok state
  | name :: rest, state => do
      let state' ← assignTopWithOffset ctx rest.length name state
      assignReturnedTops ctx rest state'

set_option maxHeartbeats 800000 in
mutual
  def Block.runOpen (program : Program) (returns : List Name) (ctx : Ctx) :
      Nat → Block → RunState → Except EVMException (Outcome × Ctx)
    | 0, _block, _state =>
        Structured.invalid
    | _fuel + 1, ⟨[]⟩, state =>
        .ok (Structured.Outcome.regular state, ctx)
    | fuel + 1, ⟨stmt :: rest⟩, state => do
        let (outcome, ctx') ← Stmt.run program returns ctx fuel stmt state
        match outcome.mode with
        | .regular =>
            Block.runOpen program returns ctx' fuel { stmts := rest }
              outcome.state
        | .brk | .cont | .leave | .halt _ =>
            .ok (outcome, ctx)
  termination_by fuel block _state => (fuel, 0, sizeOf block)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Block.runScoped (program : Program) (returns : List Name) (ctx : Ctx)
      (block : Block) (fuel : Nat) (state : RunState) :
      Except EVMException Outcome := do
    let (outcome, finalCtx) ← Block.runOpen program returns ctx fuel block state
    match outcome.mode with
    | .regular =>
        let state' ← Locals.Direct.Ctx.runCleanupTo finalCtx
          ctx.layout.length outcome.state
        .ok (Structured.Outcome.regular state')
    | .brk | .cont | .leave | .halt _ =>
        .ok outcome
  termination_by (fuel, 1, sizeOf block)
  decreasing_by
    simp_wf
    exact Prod.Lex.right fuel
      (Prod.Lex.left (sizeOf block) (sizeOf block) (by omega))

  def FunDef.runBody (program : Program) (fn : FunDef) :
      Nat → RunState → Except EVMException Outcome
    | 0, _state =>
        Structured.invalid
    | fuel + 1, state => do
        let entryCtx :=
          Locals.Ctx.procEntryWithLayoutAndRetc
            fn.params.reverse fn.returns.length
        let (stateAfterInit, initCtx) ← initReturns fn.returns entryCtx state
        let (bodyOutcome, bodyCtx) ←
          Block.runOpen program fn.returns initCtx fuel fn.body stateAfterInit
        match bodyOutcome.mode with
        | .regular =>
            let stateAfterReturns ← pushReturns bodyCtx fn.returns
              bodyOutcome.state
            let stateAfterCleanup ←
              Locals.Direct.Ctx.runCleanupToPreserving bodyCtx
                fn.returns.length 0 stateAfterReturns
            .ok (Structured.Outcome.regular stateAfterCleanup)
        | .brk | .cont =>
            Structured.invalid
        | .leave | .halt _ =>
            .ok bodyOutcome
  termination_by fuel _state => (fuel, 2, sizeOf fn.body)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Stmt.runForLoop (program : Program) (returns : List Name)
      (loopCtx : Ctx) (cond : Expr 1) (postBase : Ctx) (post : Block)
      (bodyBase : Ctx) (body : Block) :
      Nat → RunState → Except EVMException Outcome
    | 0, _state =>
        Structured.invalid
    | fuel + 1, state =>
        match Locals.Direct.Expr.runCondition loopCtx cond state with
        | .error err => .error err
        | .ok (stateAfterCond, condTrue) =>
            if condTrue then
              match Block.runScoped program returns bodyBase body fuel
                  stateAfterCond with
              | .error err => .error err
              | .ok bodyOutcome =>
                  match bodyOutcome.mode with
                  | .brk =>
                      .ok (Structured.Outcome.regular bodyOutcome.state)
                  | .regular | .cont =>
                      match Block.runScoped program returns postBase post fuel
                          bodyOutcome.state with
                      | .error err => .error err
                      | .ok postOutcome =>
                          match postOutcome.mode with
                          | .regular =>
                              Stmt.runForLoop program returns loopCtx cond
                                postBase post bodyBase body fuel
                                postOutcome.state
                          | .brk | .cont =>
                              Structured.invalid
                          | .leave | .halt _ =>
                              .ok postOutcome
                  | .leave | .halt _ =>
                      .ok bodyOutcome
            else
              .ok (Structured.Outcome.regular stateAfterCond)
  termination_by fuel _state => (fuel, 3, 0)
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def Stmt.run (program : Program) (returns : List Name) (ctx : Ctx) :
      Nat → Stmt → RunState → Except EVMException (Outcome × Ctx)
    | _fuel, .expr expr, state => do
        let state' ← Locals.Direct.Expr.runState ctx expr state
        .ok (Structured.Outcome.regular state', ctx)
    | _fuel, .let_ name value, state => do
        let state' ← Locals.Direct.Expr.runState ctx value state
        .ok (Structured.Outcome.regular state', ctx.withLayout (name :: ctx.layout))
    | _fuel, .assign name value, state => do
        let stateAfterValue ← Locals.Direct.Expr.runState ctx value state
        let stateAfterAssign ← assignTop ctx name stateAfterValue
        .ok (Structured.Outcome.regular stateAfterAssign, ctx)
    | fuel, .block body, state => do
        let outcome ← Block.runScoped program returns ctx body fuel state
        .ok (outcome, ctx)
    | 0, .if_ _cond _body, _state =>
        Structured.invalid
    | fuel + 1, .if_ cond body, state =>
        match Locals.Direct.Expr.runCondition ctx cond state with
        | .error err => .error err
        | .ok (stateAfterCond, condTrue) =>
            if condTrue then do
              let outcome ← Block.runScoped program returns ctx body fuel
                stateAfterCond
              .ok (outcome, ctx)
            else
              .ok (Structured.Outcome.regular stateAfterCond, ctx)
    | 0, .switch _scrutinee _cases _defaultBody, _state =>
        Structured.invalid
    | fuel + 1, .switch scrutinee cases defaultBody, state => do
        let stateAfterScrutinee ← Locals.Direct.Expr.runState ctx scrutinee state
        let (stack, value) ← stateAfterScrutinee.evm.stack.pop.elim
          Structured.invalid pure
        let stateAfterPop :=
          stateAfterScrutinee.withEVM
            { stateAfterScrutinee.evm with stack := stack }
        match Switch.select value cases defaultBody with
        | none => .ok (Structured.Outcome.regular stateAfterPop, ctx)
        | some body =>
            let outcome ← Block.runScoped program returns ctx body fuel
              stateAfterPop
            .ok (outcome, ctx)
    | 0, .for_ _init _cond _post _body, _state =>
        Structured.invalid
    | fuel + 1, .for_ init cond post body, state => do
        let initBase := ctx.withoutLoopControl
        let (initOutcome, initCtx) ←
          Block.runOpen program returns initBase fuel init state
        match initOutcome.mode with
        | .regular =>
            let postBase := initCtx.withoutLoopControl
            let bodyBase := initCtx.withLoopControl initCtx.layout.length
            let loopOutcome ←
              Stmt.runForLoop program returns initCtx cond postBase post
                bodyBase body fuel initOutcome.state
            match loopOutcome.mode with
            | .regular =>
                let state' ← Locals.Direct.Ctx.runCleanupTo initCtx
                  ctx.layout.length loopOutcome.state
                .ok (Structured.Outcome.regular state', ctx)
            | .brk | .cont =>
                Structured.invalid
            | .leave | .halt _ =>
                .ok (loopOutcome, ctx)
        | .brk | .cont =>
            Structured.invalid
        | .leave | .halt _ =>
            .ok (initOutcome, ctx)
    | _fuel, .brk, state => do
        let target ← ctx.breakDepth?.elim Structured.invalid pure
        let state' ← Locals.Direct.Ctx.runCleanupTo ctx target state
        .ok (Structured.Outcome.brk state', ctx)
    | _fuel, .cont, state => do
        let target ← ctx.continueDepth?.elim Structured.invalid pure
        let state' ← Locals.Direct.Ctx.runCleanupTo ctx target state
        .ok (Structured.Outcome.cont state', ctx)
    | _fuel, .leave, state => do
        let stateAfterReturns ← pushReturns ctx returns state
        let target ← ctx.leaveDepth?.elim Structured.invalid pure
        let state' ←
          Locals.Direct.Ctx.runCleanupToPreserving ctx ctx.leaveRetc target
            stateAfterReturns
        match state'.returns with
        | [] => Structured.invalid
        | _ :: _ => .ok (Structured.Outcome.leave state', ctx)
    | 0, .call _targets _functionName _args, _state =>
        Structured.invalid
    | fuel + 1, .call targets functionName args, state => do
        let stateAfterArgs ← evalArgs ctx args state
        let fn ← (FunList.find? functionName program.functions).elim
          Structured.invalid pure
        let (argStack, callerStack) ←
          (Structured.StackFrame.splitArgs? fn.params.length
            stateAfterArgs.evm.stack).elim Structured.invalid pure
        let callState :=
          (stateAfterArgs.withEVM { stateAfterArgs.evm with stack := argStack })
            |>.pushReturn callerStack fn.returns.length
        let outcome ← FunDef.runBody program fn fuel callState
        match outcome.mode with
        | .regular | .leave =>
            let (frame, returned) ← outcome.state.popReturn?.elim
              Structured.invalid pure
            let stack ← (Structured.StackFrame.attachReturns? frame
              outcome.state.evm.stack).elim Structured.invalid pure
            let stateWithReturns :=
              returned.withEVM { outcome.state.evm with stack := stack }
            let stateAfterAssign ← assignReturnedTops ctx targets.reverse
              stateWithReturns
            .ok (Structured.Outcome.regular stateAfterAssign, ctx)
        | .brk | .cont =>
            Structured.invalid
        | .halt kind =>
            .ok (Structured.Outcome.halt kind outcome.state, ctx)
    | _fuel, .terminal kind, state => do
        let stateAfterCleanup ← Locals.Direct.Ctx.runCleanupAll ctx state
        let evm ← Structured.Terminal.step kind stateAfterCleanup.evm
        .ok (Structured.Outcome.halt kind (stateAfterCleanup.withEVM evm), ctx)
    | _fuel, .terminalArgs kind args, state => do
        let evmAfterArgs ← Locals.Direct.Expr.ExprSeq.runCode ctx 0 args
          state.evm
        let evm ← Structured.Terminal.step kind evmAfterArgs
        .ok (Structured.Outcome.halt kind (state.withEVM evm), ctx)
  termination_by fuel stmt _state => (fuel, 4, sizeOf stmt)
  decreasing_by
    all_goals simp_wf
    all_goals
      first
      | omega
      | exact Prod.Lex.right _
          (Prod.Lex.left _ _ (by omega))
end

namespace Program

def runState (fuel : Nat) (program : Program) (state : RunState) :
    Except EVMException Outcome :=
  Block.runScoped program [] Locals.Ctx.initial program.body fuel state

def run (fuel : Nat) (program : Program) (state : EVMState) :
    Except EVMException Outcome :=
  runState fuel program (Structured.RunState.initial state)

end Program

end Direct

namespace Program

def run (fuel : Nat) (program : Program) (state : EVMState) :
    Except EVMException Outcome :=
  Direct.Program.run fuel program state

inductive Eval :
    Nat → Program → EVMState → Outcome → Prop where
  | ofRun {fuel : Nat} {program : Program} {initial : EVMState}
      {outcome : Outcome}
      (hRun : run fuel program initial = .ok outcome) :
      Eval fuel program initial outcome

theorem eval_of_run {fuel : Nat} {program : Program}
    {initial : EVMState} {outcome : Outcome}
    (hRun : run fuel program initial = .ok outcome) :
    Eval fuel program initial outcome := by
  exact Eval.ofRun hRun

end Program

namespace Inline
namespace Program

def run (fuel : Nat) (program : Functions.Program) (state : EVMState) :
    Except EVMException Outcome :=
  Functions.Program.run fuel program state

inductive Eval :
    Nat → Functions.Program → EVMState → Outcome → Prop where
  | ofFunctions {fuel : Nat} {program : Functions.Program}
      {initial : EVMState} {outcome : Outcome}
      (hRun : Functions.Program.run fuel program initial = .ok outcome) :
      Eval fuel program initial outcome

end Program
end Inline

end Functions
end EvmCompiler
