import EvmCompiler.Yul.Syntax
import EvmCompiler.Yul.Primitive
import EvmCompiler.Objects.Compiler

namespace EvmCompiler
namespace Yul

namespace ObjectBuiltin

def unsupported? : Name → Bool
  | "datasize" => true
  | "dataoffset" => true
  | "datacopy" => true
  | "setimmutable" => true
  | "loadimmutable" => true
  | "linkersymbol" => true
  | "memoryguard" => true
  | _ => false

end ObjectBuiltin

def identName (name : EvmYul.Identifier) : Name :=
  name

def identNames (names : List EvmYul.Identifier) : List Name :=
  names.map identName

theorem identNames_eq_self (names : List EvmYul.Identifier) :
    identNames names = names := by
  induction names with
  | nil =>
      rfl
  | cons head tail ih =>
      simp only [identNames, List.map_cons] at ih ⊢
      rw [ih]
      rfl

namespace Fresh

structure State where
  used : List Name

def initial (used : List Name) : State where
  used := used

def tempPrefix : String :=
  "__evm_compiler_tmp_"

def tempName (idx : Nat) : Name :=
  tempPrefix ++ toString idx

def freshAux (used : List Name) : Nat → Nat → Option Name
  | _idx, 0 => none
  | idx, fuel + 1 =>
      let candidate := tempName idx
      if used.contains candidate then
        freshAux used (idx + 1) fuel
      else
        some candidate

def fresh? (state : State) : Option (Name × State) := do
  let name ← freshAux state.used 0 (state.used.length + 1)
  some (name, { used := name :: state.used })

def Extends (before after : State) : Prop :=
  ∀ name, name ∈ before.used → name ∈ after.used

theorem Extends.refl (state : State) :
    Extends state state := by
  intro name hMem
  exact hMem

theorem Extends.trans
    {first second third : State}
    (hFirst : Extends first second)
    (hSecond : Extends second third) :
    Extends first third := by
  intro name hMem
  exact hSecond name (hFirst name hMem)

theorem freshAux_not_mem
    {used : List Name} {idx fuel : Nat} {name : Name}
    (hFresh : freshAux used idx fuel = some name) :
    name ∉ used := by
  induction fuel generalizing idx with
  | zero =>
      simp [freshAux] at hFresh
  | succ fuel ih =>
      simp only [freshAux] at hFresh
      split at hFresh
      · rename_i hContains
        exact ih hFresh
      · rename_i hContains
        injection hFresh with hName
        rw [← hName]
        simpa using hContains

theorem fresh?_components
    {state state' : State} {name : Name}
    (hFresh : fresh? state = some (name, state')) :
    state'.used = name :: state.used ∧ name ∉ state.used := by
  unfold fresh? at hFresh
  cases hAux :
      freshAux state.used 0 (state.used.length + 1) with
  | none =>
      simp [hAux] at hFresh
  | some freshName =>
      simp [hAux] at hFresh
      rcases hFresh with ⟨rfl, rfl⟩
      exact ⟨rfl, freshAux_not_mem hAux⟩

theorem extends_of_fresh?
    {state state' : State} {name : Name}
    (hFresh : fresh? state = some (name, state')) :
    Extends state state' := by
  obtain ⟨hUsed, _hNotMem⟩ := fresh?_components hFresh
  intro key hMem
  rw [hUsed]
  exact List.mem_cons_of_mem name hMem

theorem not_mem_of_fresh?
    {state state' : State} {name : Name}
    (hFresh : fresh? state = some (name, state')) :
    name ∉ state.used :=
  (fresh?_components hFresh).2

def freshMany? : Nat → State → Option (List Name × State)
  | 0, state => some ([], state)
  | count + 1, state => do
      let (name, state') ← fresh? state
      let (names, state'') ← freshMany? count state'
      some (name :: names, state'')

end Fresh

namespace Expr

def cast {m n : Nat} (h : m = n) (expr : Locals.Expr m) :
    Locals.Expr n := by
  cases h
  exact expr

def seqCast {m n : Nat} (h : m = n) (exprs : Locals.ExprSeq m) :
    Locals.ExprSeq n := by
  cases h
  exact exprs

def List.toSeq? :
    List (Locals.Expr 1) → (results : Nat) → Option (Locals.ExprSeq results)
  | [], 0 => some .nil
  | head :: rest, Nat.succ fuel => do
      let tail ← List.toSeq? rest fuel
      some (seqCast (by simp [Nat.add_comm])
        (Locals.ExprSeq.cons (left := 1) (right := fuel) head tail))
  | _, _ => none

/--
Build the expression sequence used as EVM stack input for primitive opcodes.

Imported Yul gives primitive arguments in source order, while EVM opcodes pop
their first argument from the top of the stack.  Reversing here means executing
`return(a, b)`, `sub(a, b)`, etc. pushes `b` before `a`, leaving `a` at the top
for the opcode.
-/
def List.toStackSeq? (exprs : List (Locals.Expr 1)) (results : Nat) :
    Option (Locals.ExprSeq results) :=
  List.toSeq? exprs.reverse results

def zero : Word :=
  EvmYul.UInt256.ofNat 0

def pureAliasPrim? : EvmYul.Operation .Yul → Bool
  | .StopArith .STOP => false
  | .StopArith _ => true
  | .CompBit _ => true
  | _ => false

mutual
  def toLocals? (results : Nat) :
      AstExpr → Option (Locals.Expr results)
    | .Lit value =>
        if h : 1 = results then
          some (cast h (.lit value))
        else
          none
    | .Var name =>
        if h : 1 = results then
          some (cast h (.var (identName name)))
        else
          none
    | .Call (.inr _functionName) _args =>
        none
    | .Call (.inl prim) args => do
        let op ← Prim.toBasicOp? prim
        let argExprs ← List.toLocals1? args
        let seq ←
          List.toStackSeq? argExprs (Expressions.Structured.BasicOp.inputs op)
        if h : Expressions.Structured.BasicOp.outputs op = results then
          some (cast h (.prim op seq))
        else
          none

  def List.toLocals1? : List AstExpr → Option (List (Locals.Expr 1))
    | [] => some []
    | expr :: rest => do
        let head ← toLocals? 1 expr
        let tail ← List.toLocals1? rest
        some (head :: tail)
end

theorem List.toLocals1?_append
    {left right : List AstExpr}
    {lowerLeft lowerRight : List (Locals.Expr 1)}
    (hLeft : List.toLocals1? left = some lowerLeft)
    (hRight : List.toLocals1? right = some lowerRight) :
    List.toLocals1? (left ++ right) =
      some (lowerLeft ++ lowerRight) := by
  induction left generalizing lowerLeft with
  | nil =>
      simp [List.toLocals1?] at hLeft
      subst lowerLeft
      simpa using hRight
  | cons head tail ih =>
      cases hHead : toLocals? 1 head with
      | none =>
          simp [List.toLocals1?, hHead] at hLeft
      | some lowerHead =>
          cases hTail : List.toLocals1? tail with
          | none =>
              simp [List.toLocals1?, hHead, hTail] at hLeft
          | some lowerTail =>
              simp [List.toLocals1?, hHead, hTail] at hLeft
              rcases hLeft with ⟨rfl⟩
              simp [List.toLocals1?, hHead,
                ih hTail]

theorem List.toLocals1?_reverse
    {exprs : List AstExpr} {lower : List (Locals.Expr 1)}
    (hLower : List.toLocals1? exprs = some lower) :
    List.toLocals1? exprs.reverse = some lower.reverse := by
  induction exprs generalizing lower with
  | nil =>
      simp [List.toLocals1?] at hLower
      subst lower
      rfl
  | cons head tail ih =>
      cases hHead : toLocals? 1 head with
      | none =>
          simp [List.toLocals1?, hHead] at hLower
      | some lowerHead =>
          cases hTail : List.toLocals1? tail with
          | none =>
              simp [List.toLocals1?, hHead, hTail] at hLower
          | some lowerTail =>
              simp [List.toLocals1?, hHead, hTail] at hLower
              rcases hLower with ⟨rfl⟩
              simpa using
                List.toLocals1?_append
                  (ih hTail)
                  (show
                    List.toLocals1? [head] = some [lowerHead] by
                    simp [List.toLocals1?, hHead])

theorem List.toSeq?_length
    {exprs : List (Locals.Expr 1)} {results : Nat}
    {seq : Locals.ExprSeq results}
    (hSeq : List.toSeq? exprs results = some seq) :
    exprs.length = results := by
  induction exprs generalizing results with
  | nil =>
      cases results <;> simp [List.toSeq?] at hSeq ⊢
  | cons head tail ih =>
      cases results with
      | zero =>
          simp [List.toSeq?] at hSeq
      | succ results =>
          cases hTail : List.toSeq? tail results with
          | none =>
              simp [List.toSeq?, hTail] at hSeq
          | some lowerTail =>
              simpa [List.toSeq?] using congrArg Nat.succ (ih hTail)

mutual
  def directCallArgSafe? : AstExpr → Bool
    | .Lit _value => true
    | .Var _name => true
    | .Call (.inl prim) args =>
        pureAliasPrim? prim && List.directCallArgsSafe? args
    | .Call (.inr _functionName) _args => false

  def List.directCallArgsSafe? : List AstExpr → Bool
    | [] => true
    | _expr :: _rest => false
end

mutual
  def pureAliasArgSafe? : AstExpr → Bool
    | .Lit _value => true
    | .Var _name => true
    | .Call (.inl prim) args =>
        pureAliasPrim? prim && List.pureAliasArgsSafe? args
    | .Call (.inr _functionName) _args => false

  def List.pureAliasArgsSafe? : List AstExpr → Bool
    | [] => true
    | expr :: rest =>
        pureAliasArgSafe? expr && List.pureAliasArgsSafe? rest
end

mutual
  /--
  Maximum number of already-evaluated sibling values above a leaf while an
  expression is evaluated in Yul's right-to-left argument order.

  A scratch-frame load needs one `DUP` beyond this pending prefix to recover
  the frame pointer. Keeping this value below 16 guarantees that the all-scratch
  backend can still reach the frame with `DUP16`.
  -/
  def pendingStackDepth : AstExpr → Nat
    | .Lit _value => 0
    | .Var _name => 0
    | .Call _kind args => List.pendingStackDepth args

  def List.pendingStackDepth : List AstExpr → Nat
    | [] => 0
    | expr :: rest =>
        max (pendingStackDepth expr + rest.length)
          (List.pendingStackDepth rest)
end

def List.directPureArgsSafe? (args : List AstExpr) : Bool :=
  List.pureAliasArgsSafe? args &&
    decide (List.pendingStackDepth args < 16)

def directPureArgSafeAt? (offset : Nat) (expr : AstExpr) : Bool :=
  pureAliasArgSafe? expr &&
    decide (pendingStackDepth expr + offset < 16)

def deferredBoundArgSafe? : AstExpr → Bool
  | .Lit _value => true
  | .Var _name => true
  | .Call _callee _args => false

theorem Prim.toUncheckedBasicOp?_eq_toBasicOp?_of_pureAlias
    {prim : EvmYul.Operation .Yul}
    (hPure : pureAliasPrim? prim = true) :
    Prim.toUncheckedBasicOp? prim = Prim.toBasicOp? prim := by
  cases prim <;>
    simp [pureAliasPrim?, Prim.toUncheckedBasicOp?] at hPure ⊢

mutual
  def lower? (results : Nat) (state : Fresh.State) :
      AstExpr →
        Option (List Functions.Stmt × Locals.Expr results × Fresh.State)
    | .Lit value =>
        if h : 1 = results then
          some ([], cast h (.lit value), state)
        else
          none
    | .Var name =>
        if h : 1 = results then
          some ([], cast h (.var (identName name)), state)
        else
          none
    | .Call (.inr functionName) args =>
        if ObjectBuiltin.unsupported? functionName then
          none
        else if h : 1 = results then do
          let (preArgs, lowerArgs, state') ←
            if List.directCallArgsSafe? args then do
              let lowerArgs ← List.toLocals1? args
              some ([], lowerArgs, state)
            else
              List.lowerBound1? state args
          let (tmp, state'') ← Fresh.fresh? state'
          some
            (preArgs ++
              [Functions.Stmt.let_ tmp (.lit zero),
                Functions.Stmt.call [tmp] functionName lowerArgs],
              cast h (.var tmp),
              state'')
        else
          none
    | .Call (.inl prim) args => do
        let op ← Prim.toBasicOp? prim
        let (preArgs, argExprs, state') ← List.lowerBound1? state args
        let seq ←
          List.toStackSeq? argExprs (Expressions.Structured.BasicOp.inputs op)
        if h : Expressions.Structured.BasicOp.outputs op = results then
          some (preArgs, cast h (.prim op seq), state')
        else
          none

  def List.lower1? (state : Fresh.State) :
      List AstExpr →
        Option (List Functions.Stmt × List (Locals.Expr 1) × Fresh.State)
    | [] => some ([], [], state)
    | expr :: rest => do
        let (preRest, lowerRest, state') ← List.lower1? state rest
        let (preHead, lowerHead, state'') ← lower? 1 state' expr
        some (preRest ++ preHead, lowerHead :: lowerRest, state'')

  /--
  Lower an argument list in imported-Yul evaluation order and bind each
  resulting value immediately into a generated local.

  `EvmYul.Yul.evalArgs` evaluates primitive/function arguments from right to
  left after the caller reverses the source argument list.  The recursive shape
  here follows the same order: lower and bind the tail before the head.  Binding
  at each argument boundary is semantically important because later argument
  evaluation may mutate memory, storage, or visible variables that an earlier
  argument already read in the source semantics.
  -/
  def List.lowerBound1? (state : Fresh.State) :
      List AstExpr →
        Option (List Functions.Stmt × List (Locals.Expr 1) × Fresh.State)
    | [] => some ([], [], state)
    | expr :: rest => do
        let (preRest, lowerRest, state') ← List.lowerBound1? state rest
        let (preHead, lowerHead, state'') ← lower? 1 state' expr
        let (tmp, state''') ← Fresh.fresh? state''
        some
          (preRest ++ preHead ++ [Functions.Stmt.let_ tmp lowerHead],
            .var tmp :: lowerRest, state''')
end

def toLocals1? (expr : AstExpr) : Option (Locals.Expr 1) :=
  toLocals? 1 expr

def toLocals0? (expr : AstExpr) : Option (Locals.Expr 0) :=
  toLocals? 0 expr

def lower1? (state : Fresh.State) (expr : AstExpr) :
    Option (List Functions.Stmt × Locals.Expr 1 × Fresh.State) :=
  lower? 1 state expr

def lower0? (state : Fresh.State) (expr : AstExpr) :
    Option (List Functions.Stmt × Locals.Expr 0 × Fresh.State) :=
  lower? 0 state expr

mutual
  def lowerUnchecked? (results : Nat) (state : Fresh.State) :
      AstExpr →
        Option (List Functions.Stmt × Locals.Expr results × Fresh.State)
    | .Lit value =>
        if h : 1 = results then
          some ([], cast h (.lit value), state)
        else
          none
    | .Var name =>
        if h : 1 = results then
          some ([], cast h (.var (identName name)), state)
        else
          none
    | .Call (.inr functionName) args =>
        if ObjectBuiltin.unsupported? functionName then
          none
        else if h : 1 = results then do
          let (preArgs, lowerArgs, state') ←
            if List.directCallArgsSafe? args then do
              let lowerArgs ← List.toLocals1? args
              some ([], lowerArgs, state)
            else
              List.lowerBound1Unchecked? state args
          let (tmp, state'') ← Fresh.fresh? state'
          some
            (preArgs ++
              [Functions.Stmt.let_ tmp (.lit zero),
                Functions.Stmt.call [tmp] functionName lowerArgs],
              cast h (.var tmp),
              state'')
        else
          none
    | .Call (.inl prim) args => do
        let op ← Prim.toUncheckedBasicOp? prim
        let (preArgs, argExprs, state') ←
          if List.directPureArgsSafe? args then do
            let argExprs ← List.toLocals1? args
            some ([], argExprs, state)
          else
            List.lowerBound1Unchecked? state args
        let seq ←
          List.toStackSeq? argExprs (Expressions.Structured.BasicOp.inputs op)
        if h : Expressions.Structured.BasicOp.outputs op = results then
          some (preArgs, cast h (.prim op seq), state')
        else
          none

  def List.lower1Unchecked? (state : Fresh.State) :
      List AstExpr →
        Option (List Functions.Stmt × List (Locals.Expr 1) × Fresh.State)
    | [] => some ([], [], state)
    | expr :: rest => do
        let (preRest, lowerRest, state') ← List.lower1Unchecked? state rest
        let (preHead, lowerHead, state'') ← lowerUnchecked? 1 state' expr
        some (preRest ++ preHead, lowerHead :: lowerRest, state'')

  def List.lowerBound1Unchecked? (state : Fresh.State) :
      List AstExpr →
        Option (List Functions.Stmt × List (Locals.Expr 1) × Fresh.State)
    | [] => some ([], [], state)
    | expr :: rest => do
        let (preRest, lowerRest, state') ← List.lowerBound1Unchecked? state rest
        let (preHead, lowerHead, state'') ← lowerUnchecked? 1 state' expr
        -- Keep a small direct window for stable leaves only. Compound
        -- expressions are materialized at their Yul evaluation boundary.
        if deferredBoundArgSafe? expr &&
            lowerRest.length < 4 then
          some (preRest ++ preHead, lowerHead :: lowerRest, state'')
        else
          let (tmp, state''') ← Fresh.fresh? state''
          some
            (preRest ++ preHead ++ [Functions.Stmt.let_ tmp lowerHead],
              .var tmp :: lowerRest, state''')
end

def lower1Unchecked? (state : Fresh.State) (expr : AstExpr) :
    Option (List Functions.Stmt × Locals.Expr 1 × Fresh.State) :=
  lowerUnchecked? 1 state expr

def lower0Unchecked? (state : Fresh.State) (expr : AstExpr) :
    Option (List Functions.Stmt × Locals.Expr 0 × Fresh.State) :=
  lowerUnchecked? 0 state expr

theorem lower1Unchecked?_direct_parts
    {offset : Nat} {state state' : Fresh.State}
    {expr : AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    (hSafe : directPureArgSafeAt? offset expr = true)
    (hLower :
      lower1Unchecked? state expr = some (pre, lower, state')) :
    pre = [] ∧ state' = state ∧ toLocals? 1 expr = some lower := by
  cases expr with
  | Lit value =>
      simp [directPureArgSafeAt?, pureAliasArgSafe?,
        lower1Unchecked?, lowerUnchecked?, cast] at hLower
      rcases hLower with ⟨rfl, rfl, rfl⟩
      simp [toLocals?, cast]
  | Var name =>
      simp [directPureArgSafeAt?, pureAliasArgSafe?,
        lower1Unchecked?, lowerUnchecked?, cast] at hLower
      rcases hLower with ⟨rfl, rfl, rfl⟩
      simp [toLocals?, cast]
  | Call callee args =>
      cases callee with
      | inr functionName =>
          simp [directPureArgSafeAt?, pureAliasArgSafe?] at hSafe
      | inl prim =>
          have hSafeParts :
              pureAliasArgSafe? (.Call (.inl prim) args) = true ∧
                decide
                    (pendingStackDepth (.Call (.inl prim) args) + offset <
                      16) =
                  true :=
            Bool.and_eq_true_iff.mp hSafe
          have hAliasParts :
              pureAliasPrim? prim = true ∧
                List.pureAliasArgsSafe? args = true := by
            simpa [pureAliasArgSafe?] using hSafeParts.1
          have hPurePrim : pureAliasPrim? prim = true := by
            exact hAliasParts.1
          have hDirect : List.directPureArgsSafe? args = true := by
            have hPureArgs :
                List.pureAliasArgsSafe? args = true := by
              exact hAliasParts.2
            have hDepth :
                List.pendingStackDepth args < 16 := by
              have hBound :
                  List.pendingStackDepth args + offset < 16 := by
                simpa [directPureArgSafeAt?, pendingStackDepth,
                  pureAliasArgSafe?, hPurePrim] using
                    (of_decide_eq_true hSafeParts.2)
              omega
            simp [List.directPureArgsSafe?, hPureArgs, hDepth]
          have hPrimEq :=
            Prim.toUncheckedBasicOp?_eq_toBasicOp?_of_pureAlias hPurePrim
          cases hOp : Prim.toBasicOp? prim with
          | none =>
              simp [lower1Unchecked?, lowerUnchecked?, hDirect, hPrimEq,
                hOp] at hLower
          | some op =>
              cases hArgs : List.toLocals1? args with
              | none =>
                  simp [lower1Unchecked?, lowerUnchecked?, hDirect, hPrimEq,
                    hOp, hArgs] at hLower
              | some lowerArgs =>
                  cases hSeq :
                      List.toStackSeq? lowerArgs
                        (Expressions.Structured.BasicOp.inputs op) with
                  | none =>
                      simp [lower1Unchecked?, lowerUnchecked?, hDirect,
                        hPrimEq, hOp, hArgs, hSeq] at hLower
                  | some seq =>
                      by_cases hOutputs :
                          Expressions.Structured.BasicOp.outputs op = 1
                      · simp [lower1Unchecked?, lowerUnchecked?, hDirect,
                          hPrimEq, hOp, hArgs, hSeq, hOutputs] at hLower
                        rcases hLower with ⟨rfl, rfl, rfl⟩
                        simp [toLocals?, hOp, hArgs, hSeq, hOutputs]
                      · simp [lower1Unchecked?, lowerUnchecked?, hDirect,
                          hPrimEq, hOp, hArgs, hSeq, hOutputs] at hLower

theorem lower1Unchecked?_deferred_parts
    {state state' : Fresh.State}
    {expr : AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    (hSafe : deferredBoundArgSafe? expr = true)
    (hLower :
      lower1Unchecked? state expr = some (pre, lower, state')) :
    pre = [] ∧ state' = state ∧ toLocals? 1 expr = some lower := by
  apply lower1Unchecked?_direct_parts
      (offset := 0) (state := state) (state' := state')
      (expr := expr) (pre := pre) (lower := lower) _ hLower
  cases expr <;>
    simp [deferredBoundArgSafe?, directPureArgSafeAt?,
      pureAliasArgSafe?, pendingStackDepth] at hSafe ⊢

theorem toLocals?_gas (results : Nat) :
    toLocals? results
        (.Call (.inl ((.StackMemFlow .GAS : EvmYul.Operation .Yul))) []) =
      none := by
  simp [toLocals?, Prim.toBasicOp?]

theorem lower?_gas (results : Nat) (state : Fresh.State) :
    lower? results state
        (.Call (.inl ((.StackMemFlow .GAS : EvmYul.Operation .Yul))) []) =
      none := by
  simp [lower?, Prim.toBasicOp?]

theorem lower1?_gas (state : Fresh.State) :
    lower1? state
        (.Call (.inl ((.StackMemFlow .GAS : EvmYul.Operation .Yul))) []) =
      none := by
  simp [lower1?, lower?_gas]

theorem lower1Unchecked?_gas (state : Fresh.State) :
    lower1Unchecked? state
        (.Call (.inl ((.StackMemFlow .GAS : EvmYul.Operation .Yul))) []) =
      some ([], (.prim .gas .nil : Locals.Expr 1), state) := by
  simp [lower1Unchecked?, lowerUnchecked?, Prim.toUncheckedBasicOp?,
    List.directPureArgsSafe?, List.pureAliasArgsSafe?,
    List.pendingStackDepth, List.toLocals1?, List.toStackSeq?,
    List.toSeq?, cast,
    Expressions.Structured.BasicOp.inputs,
    Expressions.Structured.BasicOp.outputs]

theorem lower1Unchecked?_msize (state : Fresh.State) :
    lower1Unchecked? state
        (.Call (.inl ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul))) []) =
      some ([], (.prim .msize .nil : Locals.Expr 1), state) := by
  simp [lower1Unchecked?, lowerUnchecked?, Prim.toUncheckedBasicOp?,
    List.directPureArgsSafe?, List.pureAliasArgsSafe?,
    List.pendingStackDepth, List.toLocals1?, List.toStackSeq?,
    List.toSeq?, cast,
    Expressions.Structured.BasicOp.inputs,
    Expressions.Structured.BasicOp.outputs]

theorem lower1?_lit (state : Fresh.State) (value : Word) :
    lower1? state (.Lit value) =
      some ([], (.lit value : Locals.Expr 1), state) := by
  simp [lower1?, lower?, cast]

theorem lower1?_var (state : Fresh.State) (name : EvmYul.Identifier) :
    lower1? state (.Var name) =
      some ([], (.var (identName name) : Locals.Expr 1), state) := by
  simp [lower1?, lower?, cast]

theorem lowerBound1?_nil (state : Fresh.State) :
    List.lowerBound1? state [] = some ([], [], state) := by
  rfl

theorem lowerBound1?_cons_components
    {state stateRest stateHead stateFresh : Fresh.State}
    {expr : AstExpr} {rest : List AstExpr}
    {preRest preHead : List Functions.Stmt}
    {lowerRest : List (Locals.Expr 1)}
    {lowerHead : Locals.Expr 1} {tmp : Name}
    (hRest :
      List.lowerBound1? state rest =
        some (preRest, lowerRest, stateRest))
    (hHead :
      lower1? stateRest expr = some (preHead, lowerHead, stateHead))
    (hFresh : Fresh.fresh? stateHead = some (tmp, stateFresh)) :
    List.lowerBound1? state (expr :: rest) =
      some
        (preRest ++ preHead ++ [Functions.Stmt.let_ tmp lowerHead],
          .var tmp :: lowerRest, stateFresh) := by
  have hHead' :
      lower? 1 stateRest expr = some (preHead, lowerHead, stateHead) := by
    simpa [lower1?] using hHead
  simp [List.lowerBound1?, hRest, hHead', hFresh]

theorem lowerBound1?_single_components
    {state stateExpr stateFresh : Fresh.State}
    {expr : AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1} {tmp : Name}
    (hExpr :
      lower1? state expr = some (pre, lower, stateExpr))
    (hFresh : Fresh.fresh? stateExpr = some (tmp, stateFresh)) :
    List.lowerBound1? state [expr] =
      some (pre ++ [Functions.Stmt.let_ tmp lower],
        [.var tmp], stateFresh) := by
  simpa using
    (lowerBound1?_cons_components
      (state := state) (stateRest := state) (stateHead := stateExpr)
      (stateFresh := stateFresh) (expr := expr) (rest := [])
      (preRest := []) (preHead := pre) (lowerRest := [])
      (lowerHead := lower) (tmp := tmp) rfl hExpr hFresh)

theorem lowerBound1?_two_components
    {state stateRight stateRightFresh stateLeft stateLeftFresh : Fresh.State}
    {left right : AstExpr}
    {preRight preLeft : List Functions.Stmt}
    {lowerRight lowerLeft : Locals.Expr 1}
    {rightTmp leftTmp : Name}
    (hRight :
      lower1? state right =
        some (preRight, lowerRight, stateRight))
    (hFreshRight :
      Fresh.fresh? stateRight = some (rightTmp, stateRightFresh))
    (hLeft :
      lower1? stateRightFresh left =
        some (preLeft, lowerLeft, stateLeft))
    (hFreshLeft :
      Fresh.fresh? stateLeft = some (leftTmp, stateLeftFresh)) :
    List.lowerBound1? state [left, right] =
      some
        ((preRight ++ [Functions.Stmt.let_ rightTmp lowerRight]) ++
          preLeft ++ [Functions.Stmt.let_ leftTmp lowerLeft],
          [.var leftTmp, .var rightTmp], stateLeftFresh) := by
  have hRest :
      List.lowerBound1? state [right] =
        some (preRight ++ [Functions.Stmt.let_ rightTmp lowerRight],
          [.var rightTmp], stateRightFresh) :=
    lowerBound1?_single_components hRight hFreshRight
  simpa [List.append_assoc] using
    (lowerBound1?_cons_components
      (state := state) (stateRest := stateRightFresh)
      (stateHead := stateLeft) (stateFresh := stateLeftFresh)
      (expr := left) (rest := [right])
      (preRest := preRight ++ [Functions.Stmt.let_ rightTmp lowerRight])
      (preHead := preLeft) (lowerRest := [.var rightTmp])
      (lowerHead := lowerLeft) (tmp := leftTmp)
      hRest hLeft hFreshLeft)

theorem lower1?_add_of_lowerBound1?_two
    {state state' : Fresh.State} {left right : AstExpr}
    {pre : List Functions.Stmt}
    {leftTmp rightTmp : Name}
    (hArgs :
      List.lowerBound1? state [left, right] =
        some (pre, [.var leftTmp, .var rightTmp], state')) :
    lower1? state
        (.Call (.inl ((.StopArith .ADD : EvmYul.Operation .Yul)))
          [left, right]) =
      some
        (pre,
          (.prim .add
            (Locals.ExprSeq.cons (.var rightTmp)
              (Locals.ExprSeq.cons (.var leftTmp) .nil)) :
            Locals.Expr 1),
          state') := by
    simp [lower1?, lower?, Prim.toBasicOp?, hArgs,
      List.toStackSeq?, List.toSeq?, cast, seqCast,
    Expressions.Structured.BasicOp.inputs,
    Expressions.Structured.BasicOp.outputs]

theorem lower1?_mul_of_lowerBound1?_two
    {state state' : Fresh.State} {left right : AstExpr}
    {pre : List Functions.Stmt}
    {leftTmp rightTmp : Name}
    (hArgs :
      List.lowerBound1? state [left, right] =
        some (pre, [.var leftTmp, .var rightTmp], state')) :
    lower1? state
        (.Call (.inl ((.StopArith .MUL : EvmYul.Operation .Yul)))
          [left, right]) =
      some
        (pre,
          (.prim .mul
            (Locals.ExprSeq.cons (.var rightTmp)
              (Locals.ExprSeq.cons (.var leftTmp) .nil)) :
            Locals.Expr 1),
          state') := by
  simp [lower1?, lower?, Prim.toBasicOp?, hArgs,
    List.toStackSeq?, List.toSeq?, cast, seqCast,
    Expressions.Structured.BasicOp.inputs,
    Expressions.Structured.BasicOp.outputs]

theorem lower1?_sub_of_lowerBound1?_two
    {state state' : Fresh.State} {left right : AstExpr}
    {pre : List Functions.Stmt}
    {leftTmp rightTmp : Name}
    (hArgs :
      List.lowerBound1? state [left, right] =
        some (pre, [.var leftTmp, .var rightTmp], state')) :
    lower1? state
        (.Call (.inl ((.StopArith .SUB : EvmYul.Operation .Yul)))
          [left, right]) =
      some
        (pre,
          (.prim .sub
            (Locals.ExprSeq.cons (.var rightTmp)
              (Locals.ExprSeq.cons (.var leftTmp) .nil)) :
            Locals.Expr 1),
          state') := by
  simp [lower1?, lower?, Prim.toBasicOp?, hArgs,
    List.toStackSeq?, List.toSeq?, cast, seqCast,
    Expressions.Structured.BasicOp.inputs,
    Expressions.Structured.BasicOp.outputs]

theorem lower1?_div_of_lowerBound1?_two
    {state state' : Fresh.State} {left right : AstExpr}
    {pre : List Functions.Stmt}
    {leftTmp rightTmp : Name}
    (hArgs :
      List.lowerBound1? state [left, right] =
        some (pre, [.var leftTmp, .var rightTmp], state')) :
    lower1? state
        (.Call (.inl ((.StopArith .DIV : EvmYul.Operation .Yul)))
          [left, right]) =
      some
        (pre,
          (.prim .div
            (Locals.ExprSeq.cons (.var rightTmp)
              (Locals.ExprSeq.cons (.var leftTmp) .nil)) :
            Locals.Expr 1),
          state') := by
  simp [lower1?, lower?, Prim.toBasicOp?, hArgs,
    List.toStackSeq?, List.toSeq?, cast, seqCast,
    Expressions.Structured.BasicOp.inputs,
    Expressions.Structured.BasicOp.outputs]

theorem lower1?_sdiv_of_lowerBound1?_two
    {state state' : Fresh.State} {left right : AstExpr}
    {pre : List Functions.Stmt}
    {leftTmp rightTmp : Name}
    (hArgs :
      List.lowerBound1? state [left, right] =
        some (pre, [.var leftTmp, .var rightTmp], state')) :
    lower1? state
        (.Call (.inl ((.StopArith .SDIV : EvmYul.Operation .Yul)))
          [left, right]) =
      some
        (pre,
          (.prim .sdiv
            (Locals.ExprSeq.cons (.var rightTmp)
              (Locals.ExprSeq.cons (.var leftTmp) .nil)) :
            Locals.Expr 1),
          state') := by
  simp [lower1?, lower?, Prim.toBasicOp?, hArgs,
    List.toStackSeq?, List.toSeq?, cast, seqCast,
    Expressions.Structured.BasicOp.inputs,
    Expressions.Structured.BasicOp.outputs]

theorem lower1?_mod_of_lowerBound1?_two
    {state state' : Fresh.State} {left right : AstExpr}
    {pre : List Functions.Stmt}
    {leftTmp rightTmp : Name}
    (hArgs :
      List.lowerBound1? state [left, right] =
        some (pre, [.var leftTmp, .var rightTmp], state')) :
    lower1? state
        (.Call (.inl ((.StopArith .MOD : EvmYul.Operation .Yul)))
          [left, right]) =
      some
        (pre,
          (.prim .mod
            (Locals.ExprSeq.cons (.var rightTmp)
              (Locals.ExprSeq.cons (.var leftTmp) .nil)) :
            Locals.Expr 1),
          state') := by
  simp [lower1?, lower?, Prim.toBasicOp?, hArgs,
    List.toStackSeq?, List.toSeq?, cast, seqCast,
    Expressions.Structured.BasicOp.inputs,
    Expressions.Structured.BasicOp.outputs]

theorem lower1?_smod_of_lowerBound1?_two
    {state state' : Fresh.State} {left right : AstExpr}
    {pre : List Functions.Stmt}
    {leftTmp rightTmp : Name}
    (hArgs :
      List.lowerBound1? state [left, right] =
        some (pre, [.var leftTmp, .var rightTmp], state')) :
    lower1? state
        (.Call (.inl ((.StopArith .SMOD : EvmYul.Operation .Yul)))
          [left, right]) =
      some
        (pre,
          (.prim .smod
            (Locals.ExprSeq.cons (.var rightTmp)
              (Locals.ExprSeq.cons (.var leftTmp) .nil)) :
            Locals.Expr 1),
          state') := by
  simp [lower1?, lower?, Prim.toBasicOp?, hArgs,
    List.toStackSeq?, List.toSeq?, cast, seqCast,
    Expressions.Structured.BasicOp.inputs,
    Expressions.Structured.BasicOp.outputs]

theorem lower1?_addmod_of_lowerBound1?_three
    {state state' : Fresh.State} {left middle right : AstExpr}
    {pre : List Functions.Stmt}
    {leftTmp middleTmp rightTmp : Name}
    (hArgs :
      List.lowerBound1? state [left, middle, right] =
        some (pre, [.var leftTmp, .var middleTmp, .var rightTmp], state')) :
    lower1? state
        (.Call (.inl ((.StopArith .ADDMOD : EvmYul.Operation .Yul)))
          [left, middle, right]) =
      some
        (pre,
          (.prim .addmod
            (Locals.ExprSeq.cons (.var rightTmp)
              (Locals.ExprSeq.cons (.var middleTmp)
                (Locals.ExprSeq.cons (.var leftTmp) .nil))) :
            Locals.Expr 1),
          state') := by
  simp [lower1?, lower?, Prim.toBasicOp?, hArgs,
    List.toStackSeq?, List.toSeq?, cast, seqCast,
    Expressions.Structured.BasicOp.inputs,
    Expressions.Structured.BasicOp.outputs]

theorem lower1?_mulmod_of_lowerBound1?_three
    {state state' : Fresh.State} {left middle right : AstExpr}
    {pre : List Functions.Stmt}
    {leftTmp middleTmp rightTmp : Name}
    (hArgs :
      List.lowerBound1? state [left, middle, right] =
        some (pre, [.var leftTmp, .var middleTmp, .var rightTmp], state')) :
    lower1? state
        (.Call (.inl ((.StopArith .MULMOD : EvmYul.Operation .Yul)))
          [left, middle, right]) =
      some
        (pre,
          (.prim .mulmod
            (Locals.ExprSeq.cons (.var rightTmp)
              (Locals.ExprSeq.cons (.var middleTmp)
                (Locals.ExprSeq.cons (.var leftTmp) .nil))) :
            Locals.Expr 1),
          state') := by
  simp [lower1?, lower?, Prim.toBasicOp?, hArgs,
    List.toStackSeq?, List.toSeq?, cast, seqCast,
    Expressions.Structured.BasicOp.inputs,
    Expressions.Structured.BasicOp.outputs]

theorem lower1?_exp_of_lowerBound1?_two
    {state state' : Fresh.State} {left right : AstExpr}
    {pre : List Functions.Stmt}
    {leftTmp rightTmp : Name}
    (hArgs :
      List.lowerBound1? state [left, right] =
        some (pre, [.var leftTmp, .var rightTmp], state')) :
    lower1? state
        (.Call (.inl ((.StopArith .EXP : EvmYul.Operation .Yul)))
          [left, right]) =
      some
        (pre,
          (.prim .exp
            (Locals.ExprSeq.cons (.var rightTmp)
              (Locals.ExprSeq.cons (.var leftTmp) .nil)) :
            Locals.Expr 1),
          state') := by
  simp [lower1?, lower?, Prim.toBasicOp?, hArgs,
    List.toStackSeq?, List.toSeq?, cast, seqCast,
    Expressions.Structured.BasicOp.inputs,
    Expressions.Structured.BasicOp.outputs]

theorem lower1?_signextend_of_lowerBound1?_two
    {state state' : Fresh.State} {left right : AstExpr}
    {pre : List Functions.Stmt}
    {leftTmp rightTmp : Name}
    (hArgs :
      List.lowerBound1? state [left, right] =
        some (pre, [.var leftTmp, .var rightTmp], state')) :
    lower1? state
        (.Call (.inl ((.StopArith .SIGNEXTEND : EvmYul.Operation .Yul)))
          [left, right]) =
      some
        (pre,
          (.prim .signextend
            (Locals.ExprSeq.cons (.var rightTmp)
              (Locals.ExprSeq.cons (.var leftTmp) .nil)) :
            Locals.Expr 1),
          state') := by
  simp [lower1?, lower?, Prim.toBasicOp?, hArgs,
    List.toStackSeq?, List.toSeq?, cast, seqCast,
    Expressions.Structured.BasicOp.inputs,
    Expressions.Structured.BasicOp.outputs]

theorem lower1?_lt_of_lowerBound1?_two
    {state state' : Fresh.State} {left right : AstExpr}
    {pre : List Functions.Stmt}
    {leftTmp rightTmp : Name}
    (hArgs :
      List.lowerBound1? state [left, right] =
        some (pre, [.var leftTmp, .var rightTmp], state')) :
    lower1? state
        (.Call (.inl ((.CompBit .LT : EvmYul.Operation .Yul)))
          [left, right]) =
      some
        (pre,
          (.prim .lt
            (Locals.ExprSeq.cons (.var rightTmp)
              (Locals.ExprSeq.cons (.var leftTmp) .nil)) :
            Locals.Expr 1),
          state') := by
  simp [lower1?, lower?, Prim.toBasicOp?, hArgs,
    List.toStackSeq?, List.toSeq?, cast, seqCast,
    Expressions.Structured.BasicOp.inputs,
    Expressions.Structured.BasicOp.outputs]

theorem lower1?_gt_of_lowerBound1?_two
    {state state' : Fresh.State} {left right : AstExpr}
    {pre : List Functions.Stmt}
    {leftTmp rightTmp : Name}
    (hArgs :
      List.lowerBound1? state [left, right] =
        some (pre, [.var leftTmp, .var rightTmp], state')) :
    lower1? state
        (.Call (.inl ((.CompBit .GT : EvmYul.Operation .Yul)))
          [left, right]) =
      some
        (pre,
          (.prim .gt
            (Locals.ExprSeq.cons (.var rightTmp)
              (Locals.ExprSeq.cons (.var leftTmp) .nil)) :
            Locals.Expr 1),
          state') := by
  simp [lower1?, lower?, Prim.toBasicOp?, hArgs,
    List.toStackSeq?, List.toSeq?, cast, seqCast,
    Expressions.Structured.BasicOp.inputs,
    Expressions.Structured.BasicOp.outputs]

theorem lower1?_slt_of_lowerBound1?_two
    {state state' : Fresh.State} {left right : AstExpr}
    {pre : List Functions.Stmt}
    {leftTmp rightTmp : Name}
    (hArgs :
      List.lowerBound1? state [left, right] =
        some (pre, [.var leftTmp, .var rightTmp], state')) :
    lower1? state
        (.Call (.inl ((.CompBit .SLT : EvmYul.Operation .Yul)))
          [left, right]) =
      some
        (pre,
          (.prim .slt
            (Locals.ExprSeq.cons (.var rightTmp)
              (Locals.ExprSeq.cons (.var leftTmp) .nil)) :
            Locals.Expr 1),
          state') := by
  simp [lower1?, lower?, Prim.toBasicOp?, hArgs,
    List.toStackSeq?, List.toSeq?, cast, seqCast,
    Expressions.Structured.BasicOp.inputs,
    Expressions.Structured.BasicOp.outputs]

theorem lower1?_sgt_of_lowerBound1?_two
    {state state' : Fresh.State} {left right : AstExpr}
    {pre : List Functions.Stmt}
    {leftTmp rightTmp : Name}
    (hArgs :
      List.lowerBound1? state [left, right] =
        some (pre, [.var leftTmp, .var rightTmp], state')) :
    lower1? state
        (.Call (.inl ((.CompBit .SGT : EvmYul.Operation .Yul)))
          [left, right]) =
      some
        (pre,
          (.prim .sgt
            (Locals.ExprSeq.cons (.var rightTmp)
              (Locals.ExprSeq.cons (.var leftTmp) .nil)) :
            Locals.Expr 1),
          state') := by
  simp [lower1?, lower?, Prim.toBasicOp?, hArgs,
    List.toStackSeq?, List.toSeq?, cast, seqCast,
    Expressions.Structured.BasicOp.inputs,
    Expressions.Structured.BasicOp.outputs]

theorem lower1?_eq_of_lowerBound1?_two
    {state state' : Fresh.State} {left right : AstExpr}
    {pre : List Functions.Stmt}
    {leftTmp rightTmp : Name}
    (hArgs :
      List.lowerBound1? state [left, right] =
        some (pre, [.var leftTmp, .var rightTmp], state')) :
    lower1? state
        (.Call (.inl ((.CompBit .EQ : EvmYul.Operation .Yul)))
          [left, right]) =
      some
        (pre,
          (.prim .eq
            (Locals.ExprSeq.cons (.var rightTmp)
              (Locals.ExprSeq.cons (.var leftTmp) .nil)) :
            Locals.Expr 1),
          state') := by
  simp [lower1?, lower?, Prim.toBasicOp?, hArgs,
    List.toStackSeq?, List.toSeq?, cast, seqCast,
    Expressions.Structured.BasicOp.inputs,
    Expressions.Structured.BasicOp.outputs]

theorem lower1?_and_of_lowerBound1?_two
    {state state' : Fresh.State} {left right : AstExpr}
    {pre : List Functions.Stmt}
    {leftTmp rightTmp : Name}
    (hArgs :
      List.lowerBound1? state [left, right] =
        some (pre, [.var leftTmp, .var rightTmp], state')) :
    lower1? state
        (.Call (.inl ((.CompBit .AND : EvmYul.Operation .Yul)))
          [left, right]) =
      some
        (pre,
          (.prim .and
            (Locals.ExprSeq.cons (.var rightTmp)
              (Locals.ExprSeq.cons (.var leftTmp) .nil)) :
            Locals.Expr 1),
          state') := by
  simp [lower1?, lower?, Prim.toBasicOp?, hArgs,
    List.toStackSeq?, List.toSeq?, cast, seqCast,
    Expressions.Structured.BasicOp.inputs,
    Expressions.Structured.BasicOp.outputs]

theorem lower1?_or_of_lowerBound1?_two
    {state state' : Fresh.State} {left right : AstExpr}
    {pre : List Functions.Stmt}
    {leftTmp rightTmp : Name}
    (hArgs :
      List.lowerBound1? state [left, right] =
        some (pre, [.var leftTmp, .var rightTmp], state')) :
    lower1? state
        (.Call (.inl ((.CompBit .OR : EvmYul.Operation .Yul)))
          [left, right]) =
      some
        (pre,
          (.prim .or
            (Locals.ExprSeq.cons (.var rightTmp)
              (Locals.ExprSeq.cons (.var leftTmp) .nil)) :
            Locals.Expr 1),
          state') := by
  simp [lower1?, lower?, Prim.toBasicOp?, hArgs,
    List.toStackSeq?, List.toSeq?, cast, seqCast,
    Expressions.Structured.BasicOp.inputs,
    Expressions.Structured.BasicOp.outputs]

theorem lower1?_xor_of_lowerBound1?_two
    {state state' : Fresh.State} {left right : AstExpr}
    {pre : List Functions.Stmt}
    {leftTmp rightTmp : Name}
    (hArgs :
      List.lowerBound1? state [left, right] =
        some (pre, [.var leftTmp, .var rightTmp], state')) :
    lower1? state
        (.Call (.inl ((.CompBit .XOR : EvmYul.Operation .Yul)))
          [left, right]) =
      some
        (pre,
          (.prim .xor
            (Locals.ExprSeq.cons (.var rightTmp)
              (Locals.ExprSeq.cons (.var leftTmp) .nil)) :
            Locals.Expr 1),
          state') := by
  simp [lower1?, lower?, Prim.toBasicOp?, hArgs,
    List.toStackSeq?, List.toSeq?, cast, seqCast,
    Expressions.Structured.BasicOp.inputs,
    Expressions.Structured.BasicOp.outputs]

theorem lower1?_byte_of_lowerBound1?_two
    {state state' : Fresh.State} {left right : AstExpr}
    {pre : List Functions.Stmt}
    {leftTmp rightTmp : Name}
    (hArgs :
      List.lowerBound1? state [left, right] =
        some (pre, [.var leftTmp, .var rightTmp], state')) :
    lower1? state
        (.Call (.inl ((.CompBit .BYTE : EvmYul.Operation .Yul)))
          [left, right]) =
      some
        (pre,
          (.prim .byte
            (Locals.ExprSeq.cons (.var rightTmp)
              (Locals.ExprSeq.cons (.var leftTmp) .nil)) :
            Locals.Expr 1),
          state') := by
  simp [lower1?, lower?, Prim.toBasicOp?, hArgs,
    List.toStackSeq?, List.toSeq?, cast, seqCast,
    Expressions.Structured.BasicOp.inputs,
    Expressions.Structured.BasicOp.outputs]

theorem lower1?_shl_of_lowerBound1?_two
    {state state' : Fresh.State} {left right : AstExpr}
    {pre : List Functions.Stmt}
    {leftTmp rightTmp : Name}
    (hArgs :
      List.lowerBound1? state [left, right] =
        some (pre, [.var leftTmp, .var rightTmp], state')) :
    lower1? state
        (.Call (.inl ((.CompBit .SHL : EvmYul.Operation .Yul)))
          [left, right]) =
      some
        (pre,
          (.prim .shl
            (Locals.ExprSeq.cons (.var rightTmp)
              (Locals.ExprSeq.cons (.var leftTmp) .nil)) :
            Locals.Expr 1),
          state') := by
  simp [lower1?, lower?, Prim.toBasicOp?, hArgs,
    List.toStackSeq?, List.toSeq?, cast, seqCast,
    Expressions.Structured.BasicOp.inputs,
    Expressions.Structured.BasicOp.outputs]

theorem lower1?_shr_of_lowerBound1?_two
    {state state' : Fresh.State} {left right : AstExpr}
    {pre : List Functions.Stmt}
    {leftTmp rightTmp : Name}
    (hArgs :
      List.lowerBound1? state [left, right] =
        some (pre, [.var leftTmp, .var rightTmp], state')) :
    lower1? state
        (.Call (.inl ((.CompBit .SHR : EvmYul.Operation .Yul)))
          [left, right]) =
      some
        (pre,
          (.prim .shr
            (Locals.ExprSeq.cons (.var rightTmp)
              (Locals.ExprSeq.cons (.var leftTmp) .nil)) :
            Locals.Expr 1),
          state') := by
  simp [lower1?, lower?, Prim.toBasicOp?, hArgs,
    List.toStackSeq?, List.toSeq?, cast, seqCast,
    Expressions.Structured.BasicOp.inputs,
    Expressions.Structured.BasicOp.outputs]

theorem lower1?_sar_of_lowerBound1?_two
    {state state' : Fresh.State} {left right : AstExpr}
    {pre : List Functions.Stmt}
    {leftTmp rightTmp : Name}
    (hArgs :
      List.lowerBound1? state [left, right] =
        some (pre, [.var leftTmp, .var rightTmp], state')) :
    lower1? state
        (.Call (.inl ((.CompBit .SAR : EvmYul.Operation .Yul)))
          [left, right]) =
      some
        (pre,
          (.prim .sar
            (Locals.ExprSeq.cons (.var rightTmp)
              (Locals.ExprSeq.cons (.var leftTmp) .nil)) :
            Locals.Expr 1),
          state') := by
  simp [lower1?, lower?, Prim.toBasicOp?, hArgs,
    List.toStackSeq?, List.toSeq?, cast, seqCast,
    Expressions.Structured.BasicOp.inputs,
    Expressions.Structured.BasicOp.outputs]

theorem lower1?_prim_of_lowerBound1?
    {state state' : Fresh.State} {prim : EvmYul.Operation .Yul}
    {args : List AstExpr} {pre : List Functions.Stmt}
    {argExprs : List (Locals.Expr 1)}
    {op : Structured.BasicOp}
    {seq : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op)}
    (hPrim : Prim.toBasicOp? prim = some op)
    (hArgs :
      List.lowerBound1? state args =
        some (pre, argExprs, state'))
    (hSeq :
      List.toStackSeq? argExprs
          (Expressions.Structured.BasicOp.inputs op) =
        some seq)
    (hOutputs : Expressions.Structured.BasicOp.outputs op = 1) :
    lower1? state (.Call (.inl prim) args) =
      some (pre, cast hOutputs (.prim op seq), state') := by
  simp [lower1?, lower?, hPrim, hArgs, hSeq, hOutputs]

theorem lower0?_prim_of_lowerBound1?
    {state state' : Fresh.State} {prim : EvmYul.Operation .Yul}
    {args : List AstExpr} {pre : List Functions.Stmt}
    {argExprs : List (Locals.Expr 1)}
    {op : Structured.BasicOp}
    {seq : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op)}
    (hPrim : Prim.toBasicOp? prim = some op)
    (hArgs :
      List.lowerBound1? state args =
        some (pre, argExprs, state'))
    (hSeq :
      List.toStackSeq? argExprs
          (Expressions.Structured.BasicOp.inputs op) =
        some seq)
    (hOutputs : Expressions.Structured.BasicOp.outputs op = 0) :
    lower0? state (.Call (.inl prim) args) =
      some (pre, cast hOutputs (.prim op seq), state') := by
  simp [lower0?, lower?, hPrim, hArgs, hSeq, hOutputs]

namespace List

inductive BoundLowering :
    Fresh.State → List AstExpr → List Functions.Stmt →
      List (Locals.Expr 1) → Fresh.State → Prop where
  | nil (state : Fresh.State) :
      BoundLowering state [] [] [] state
  | cons
      {state stateRest stateHead stateFresh : Fresh.State}
      {expr : AstExpr} {rest : List AstExpr}
      {preRest preHead : List Functions.Stmt}
      {lowerRest : List (Locals.Expr 1)}
      {lowerHead : Locals.Expr 1} {tmp : Name}
      (hRest :
        BoundLowering state rest preRest lowerRest stateRest)
      (hHead :
        EvmCompiler.Yul.Expr.lower1? stateRest expr =
          some (preHead, lowerHead, stateHead))
      (hFresh : Fresh.fresh? stateHead = some (tmp, stateFresh)) :
      BoundLowering state (expr :: rest)
        (preRest ++ preHead ++ [Functions.Stmt.let_ tmp lowerHead])
        (.var tmp :: lowerRest) stateFresh

namespace BoundLowering

theorem to_lowerBound1?
    {state state' : Fresh.State} {args : List AstExpr}
    {pre : List Functions.Stmt} {lowerArgs : List (Locals.Expr 1)}
    (hLowering :
      BoundLowering state args pre lowerArgs state') :
    lowerBound1? state args = some (pre, lowerArgs, state') := by
  induction hLowering with
  | nil =>
      rfl
  | cons hRest hHead hFresh ih =>
      exact EvmCompiler.Yul.Expr.lowerBound1?_cons_components ih hHead hFresh

theorem length_lowerArgs_eq
    {state state' : Fresh.State} {args : List AstExpr}
    {pre : List Functions.Stmt} {lowerArgs : List (Locals.Expr 1)}
    (hLowering :
      BoundLowering state args pre lowerArgs state') :
    lowerArgs.length = args.length := by
  induction hLowering with
  | nil =>
      rfl
  | cons _hRest _hHead _hFresh ih =>
      simp [ih]

theorem lowerArgs_vars
    {state state' : Fresh.State} {args : List AstExpr}
    {pre : List Functions.Stmt} {lowerArgs : List (Locals.Expr 1)}
    (hLowering :
      BoundLowering state args pre lowerArgs state') :
    ∃ names : List Name,
      lowerArgs = names.map (fun name => (.var name : Locals.Expr 1)) := by
  induction hLowering with
  | nil =>
      exact ⟨[], rfl⟩
  | @cons stateRest stateHead stateFresh expr rest preRest preHead lowerRest
      lowerHead tmp hRest _hHead _hFresh ih =>
      rcases ih with ⟨names, hNames⟩
      exact ⟨tmp :: names, by simp [hNames]⟩

end BoundLowering

theorem boundLowering_of_lowerBound1?
    {state state' : Fresh.State} {args : List AstExpr}
    {pre : List Functions.Stmt} {lowerArgs : List (Locals.Expr 1)}
    (hLower :
      lowerBound1? state args = some (pre, lowerArgs, state')) :
    BoundLowering state args pre lowerArgs state' := by
  induction args generalizing state pre lowerArgs state' with
  | nil =>
      have hTuple :
          ([], [], state) = (pre, lowerArgs, state') := by
        simpa [lowerBound1?] using hLower
      cases hTuple
      exact BoundLowering.nil state
  | cons expr rest ih =>
      simp [lowerBound1?] at hLower
      cases hRest : lowerBound1? state rest with
      | none =>
          simp [hRest] at hLower
      | some restResult =>
          rcases restResult with ⟨preRest, lowerRest, stateRest⟩
          cases hHead : EvmCompiler.Yul.Expr.lower? 1 stateRest expr with
          | none =>
              simp [hRest, hHead] at hLower
          | some headResult =>
              rcases headResult with ⟨preHead, lowerHead, stateHead⟩
              cases hFresh : Fresh.fresh? stateHead with
              | none =>
                  simp [hRest, hHead, hFresh] at hLower
              | some freshResult =>
                  rcases freshResult with ⟨tmp, stateFresh⟩
                  have hTuple :
                      (preRest ++ preHead ++
                          [Functions.Stmt.let_ tmp lowerHead],
                        .var tmp :: lowerRest, stateFresh) =
                        (pre, lowerArgs, state') := by
                    simpa [lowerBound1?, hRest, hHead, hFresh] using hLower
                  cases hTuple
                  have hHeadLower1 :
                      EvmCompiler.Yul.Expr.lower1? stateRest expr =
                        some (preHead, lowerHead, stateHead) := by
                    simpa [EvmCompiler.Yul.Expr.lower1?] using hHead
                  exact
                    BoundLowering.cons (expr := expr)
                      (ih hRest) hHeadLower1 hFresh

theorem lowerBound1?_length_lowerArgs_eq
    {state state' : Fresh.State} {args : List AstExpr}
    {pre : List Functions.Stmt} {lowerArgs : List (Locals.Expr 1)}
    (hLower :
      lowerBound1? state args = some (pre, lowerArgs, state')) :
    lowerArgs.length = args.length :=
  BoundLowering.length_lowerArgs_eq
    (boundLowering_of_lowerBound1? hLower)

theorem lowerBound1?_lowerArgs_vars
    {state state' : Fresh.State} {args : List AstExpr}
    {pre : List Functions.Stmt} {lowerArgs : List (Locals.Expr 1)}
    (hLower :
      lowerBound1? state args = some (pre, lowerArgs, state')) :
    ∃ names : List Name,
      lowerArgs = names.map (fun name => (.var name : Locals.Expr 1)) :=
  BoundLowering.lowerArgs_vars
    (boundLowering_of_lowerBound1? hLower)

inductive UncheckedBoundLowering :
    Fresh.State → List AstExpr → List Functions.Stmt →
      List (Locals.Expr 1) → Fresh.State → Prop where
  | nil (state : Fresh.State) :
      UncheckedBoundLowering state [] [] [] state
  | direct
      {state stateRest stateHead : Fresh.State}
      {expr : AstExpr} {rest : List AstExpr}
      {preRest preHead : List Functions.Stmt}
      {lowerRest : List (Locals.Expr 1)}
      {lowerHead : Locals.Expr 1}
      (hRest :
        UncheckedBoundLowering state rest preRest lowerRest stateRest)
      (hHead :
        EvmCompiler.Yul.Expr.lower1Unchecked? stateRest expr =
          some (preHead, lowerHead, stateHead))
      (hDirect :
        deferredBoundArgSafe? expr = true ∧
          lowerRest.length < 4) :
      UncheckedBoundLowering state (expr :: rest)
        (preRest ++ preHead) (lowerHead :: lowerRest) stateHead
  | bound
      {state stateRest stateHead stateFresh : Fresh.State}
      {expr : AstExpr} {rest : List AstExpr}
      {preRest preHead : List Functions.Stmt}
      {lowerRest : List (Locals.Expr 1)}
      {lowerHead : Locals.Expr 1} {tmp : Name}
      (hRest :
        UncheckedBoundLowering state rest preRest lowerRest stateRest)
      (hHead :
        EvmCompiler.Yul.Expr.lower1Unchecked? stateRest expr =
          some (preHead, lowerHead, stateHead))
      (hDirect :
        ¬(deferredBoundArgSafe? expr = true ∧
          lowerRest.length < 4))
      (hFresh : Fresh.fresh? stateHead = some (tmp, stateFresh)) :
      UncheckedBoundLowering state (expr :: rest)
        (preRest ++ preHead ++ [Functions.Stmt.let_ tmp lowerHead])
        (.var tmp :: lowerRest) stateFresh

namespace UncheckedBoundLowering

theorem to_lowerBound1Unchecked?
    {state state' : Fresh.State} {args : List AstExpr}
    {pre : List Functions.Stmt} {lowerArgs : List (Locals.Expr 1)}
    (hLowering :
      UncheckedBoundLowering state args pre lowerArgs state') :
    lowerBound1Unchecked? state args =
      some (pre, lowerArgs, state') := by
  induction hLowering with
  | nil =>
      rfl
  | @direct stateRest stateHead expr rest preRest preHead lowerRest
      lowerHead hRest hHead hDirect ih =>
      have hHead' :
          lowerUnchecked? 1 stateRest expr =
            some (preHead, lowerHead, stateHead) := by
        simpa [lower1Unchecked?] using hHead
      simp [lowerBound1Unchecked?, ih, hHead', hDirect]
  | @bound stateRest stateHead stateFresh expr rest preRest preHead
      lowerRest lowerHead tmp hRest hHead hDirect hFresh ih =>
      have hHead' :
          lowerUnchecked? 1 stateRest expr =
            some (preHead, lowerHead, stateHead) := by
        simpa [lower1Unchecked?] using hHead
      simp [lowerBound1Unchecked?, ih, hHead', hDirect, hFresh]

theorem length_lowerArgs_eq
    {state state' : Fresh.State} {args : List AstExpr}
    {pre : List Functions.Stmt} {lowerArgs : List (Locals.Expr 1)}
    (hLowering :
      UncheckedBoundLowering state args pre lowerArgs state') :
    lowerArgs.length = args.length := by
  induction hLowering with
  | nil =>
      rfl
  | direct _hRest _hHead _hDirect ih =>
      simp [ih]
  | bound _hRest _hHead _hDirect _hFresh ih =>
      simp [ih]

theorem stateExtends
    {state state' : Fresh.State} {args : List AstExpr}
    {pre : List Functions.Stmt} {lowerArgs : List (Locals.Expr 1)}
    (hLowering :
      UncheckedBoundLowering state args pre lowerArgs state')
    (hExpr :
      ∀ {before after : Fresh.State} {expr : AstExpr}
        {exprPre : List Functions.Stmt} {lower : Locals.Expr 1},
        EvmCompiler.Yul.Expr.lower1Unchecked? before expr =
            some (exprPre, lower, after) →
          Fresh.Extends before after) :
    Fresh.Extends state state' := by
  induction hLowering with
  | nil =>
      exact Fresh.Extends.refl _
  | direct _hRest hHead _hDirect ih =>
      exact Fresh.Extends.trans ih (hExpr hHead)
  | bound _hRest hHead _hDirect hFresh ih =>
      exact
        Fresh.Extends.trans
          (Fresh.Extends.trans ih (hExpr hHead))
          (Fresh.extends_of_fresh? hFresh)

end UncheckedBoundLowering

theorem uncheckedBoundLowering_of_lowerBound1Unchecked?
    {state state' : Fresh.State} {args : List AstExpr}
    {pre : List Functions.Stmt} {lowerArgs : List (Locals.Expr 1)}
    (hLower :
      lowerBound1Unchecked? state args =
        some (pre, lowerArgs, state')) :
    UncheckedBoundLowering state args pre lowerArgs state' := by
  induction args generalizing state pre lowerArgs state' with
  | nil =>
      have hTuple :
          ([], [], state) = (pre, lowerArgs, state') := by
        simpa [lowerBound1Unchecked?] using hLower
      cases hTuple
      exact UncheckedBoundLowering.nil state
  | cons expr rest ih =>
      simp [lowerBound1Unchecked?] at hLower
      cases hRest : lowerBound1Unchecked? state rest with
      | none =>
          simp [hRest] at hLower
      | some restResult =>
          rcases restResult with ⟨preRest, lowerRest, stateRest⟩
          cases hHead :
              EvmCompiler.Yul.Expr.lowerUnchecked? 1 stateRest expr with
          | none =>
              simp [hRest, hHead] at hLower
          | some headResult =>
              rcases headResult with ⟨preHead, lowerHead, stateHead⟩
              by_cases hDirect :
                  deferredBoundArgSafe? expr = true ∧
                    lowerRest.length < 4
              · have hHeadLower1 :
                    EvmCompiler.Yul.Expr.lower1Unchecked? stateRest expr =
                      some (preHead, lowerHead, stateHead) := by
                  simpa [EvmCompiler.Yul.Expr.lower1Unchecked?] using hHead
                have hTuple :
                    (preRest ++ preHead, lowerHead :: lowerRest, stateHead) =
                      (pre, lowerArgs, state') := by
                  simpa [lowerBound1Unchecked?, hRest, hHead, hDirect]
                    using hLower
                cases hTuple
                exact
                  UncheckedBoundLowering.direct
                    (ih hRest) hHeadLower1 hDirect
              · cases hFresh : Fresh.fresh? stateHead with
                | none =>
                    simp [hRest, hHead, hDirect, hFresh] at hLower
                | some freshResult =>
                    rcases freshResult with ⟨tmp, stateFresh⟩
                    have hTuple :
                        (preRest ++ preHead ++
                            [Functions.Stmt.let_ tmp lowerHead],
                          .var tmp :: lowerRest, stateFresh) =
                          (pre, lowerArgs, state') := by
                      simpa [lowerBound1Unchecked?, hRest, hHead,
                        hDirect, hFresh] using hLower
                    cases hTuple
                    have hHeadLower1 :
                        EvmCompiler.Yul.Expr.lower1Unchecked? stateRest expr =
                          some (preHead, lowerHead, stateHead) := by
                      simpa [EvmCompiler.Yul.Expr.lower1Unchecked?] using hHead
                    exact
                      UncheckedBoundLowering.bound
                        (ih hRest) hHeadLower1 hDirect hFresh

theorem lowerBound1Unchecked?_length_lowerArgs_eq
    {state state' : Fresh.State} {args : List AstExpr}
    {pre : List Functions.Stmt} {lowerArgs : List (Locals.Expr 1)}
    (hLower :
      lowerBound1Unchecked? state args =
        some (pre, lowerArgs, state')) :
    lowerArgs.length = args.length :=
  UncheckedBoundLowering.length_lowerArgs_eq
    (uncheckedBoundLowering_of_lowerBound1Unchecked? hLower)

end List

inductive UncheckedCallArgsLowering :
    Fresh.State → List AstExpr → List Functions.Stmt →
      List (Locals.Expr 1) → Fresh.State → Prop where
  | empty (state : Fresh.State) :
      UncheckedCallArgsLowering state [] [] [] state
  | bound
      {state state' : Fresh.State} {args : List AstExpr}
      {pre : List Functions.Stmt} {lowerArgs : List (Locals.Expr 1)}
      (hNonempty : args ≠ [])
      (hLowering :
        List.UncheckedBoundLowering state args pre lowerArgs state') :
      UncheckedCallArgsLowering state args pre lowerArgs state'

inductive UncheckedFunctionCallLowering :
    Fresh.State → Name → List AstExpr → List Functions.Stmt →
      Locals.Expr 1 → Fresh.State → Prop where
  | call
      {state argsState final : Fresh.State}
      {functionName tmp : Name} {args : List AstExpr}
      {preArgs : List Functions.Stmt}
      {lowerArgs : List (Locals.Expr 1)}
      (hSupported : ObjectBuiltin.unsupported? functionName = false)
      (hArgs :
        UncheckedCallArgsLowering state args preArgs lowerArgs argsState)
      (hFresh : Fresh.fresh? argsState = some (tmp, final)) :
      UncheckedFunctionCallLowering state functionName args
        (preArgs ++
          [Functions.Stmt.let_ tmp (.lit zero),
            Functions.Stmt.call [tmp] functionName lowerArgs])
        (.var tmp) final

theorem uncheckedFunctionCallLowering_of_lower1Unchecked?
    {state final : Fresh.State} {functionName : Name}
    {args : List AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    (hLower :
      lower1Unchecked? state (.Call (.inr functionName) args) =
        some (pre, lower, final)) :
    UncheckedFunctionCallLowering state functionName args pre lower final := by
  unfold lower1Unchecked? lowerUnchecked? at hLower
  by_cases hUnsupported : ObjectBuiltin.unsupported? functionName
  · simp [hUnsupported] at hLower
  · cases args with
    | nil =>
        cases hFresh : Fresh.fresh? state with
        | none =>
            simp [hUnsupported, List.directCallArgsSafe?,
              List.toLocals1?, hFresh] at hLower
        | some result =>
            rcases result with ⟨tmp, finalState⟩
            have hTuple :
                ([Functions.Stmt.let_ tmp (.lit zero),
                    Functions.Stmt.call [tmp] functionName []],
                  (.var tmp : Locals.Expr 1), finalState) =
                (pre, lower, final) := by
              simpa [hUnsupported, List.directCallArgsSafe?,
                List.toLocals1?, hFresh] using hLower
            cases hTuple
            exact
              UncheckedFunctionCallLowering.call
                (by simpa using hUnsupported)
                (UncheckedCallArgsLowering.empty state) hFresh
    | cons head tail =>
        cases hArgs :
            List.lowerBound1Unchecked? state (head :: tail) with
        | none =>
            simp [hUnsupported, List.directCallArgsSafe?, hArgs] at hLower
        | some result =>
            rcases result with ⟨preArgs, lowerArgs, argsState⟩
            cases hFresh : Fresh.fresh? argsState with
            | none =>
                simp [hUnsupported, List.directCallArgsSafe?,
                  hArgs, hFresh] at hLower
            | some result =>
                rcases result with ⟨tmp, finalState⟩
                have hTuple :
                    (preArgs ++
                        [Functions.Stmt.let_ tmp (.lit zero),
                          Functions.Stmt.call [tmp] functionName lowerArgs],
                      (.var tmp : Locals.Expr 1), finalState) =
                    (pre, lower, final) := by
                  simpa [hUnsupported, List.directCallArgsSafe?,
                    hArgs, hFresh] using hLower
                cases hTuple
                exact
                  UncheckedFunctionCallLowering.call
                    (by simpa using hUnsupported)
                    (UncheckedCallArgsLowering.bound
                      (by simp)
                      (List.uncheckedBoundLowering_of_lowerBound1Unchecked?
                        hArgs))
                    hFresh

theorem UncheckedFunctionCallLowering.parts
    {state final : Fresh.State} {functionName : Name}
    {args : List AstExpr} {pre : List Functions.Stmt}
    {lower : Locals.Expr 1}
    (hLowering :
      UncheckedFunctionCallLowering state functionName args
        pre lower final) :
    ∃ argsState tmp preArgs lowerArgs,
      UncheckedCallArgsLowering state args
        preArgs lowerArgs argsState ∧
      Fresh.fresh? argsState = some (tmp, final) ∧
      pre =
        preArgs ++
          [Functions.Stmt.let_ tmp (.lit zero),
            Functions.Stmt.call [tmp] functionName lowerArgs] ∧
      lower = .var tmp := by
  cases hLowering with
  | call _hSupported hArgs hFresh =>
      exact ⟨_, _, _, _, hArgs, hFresh, rfl, rfl⟩

def Supported (results : Nat) (expr : AstExpr) : Prop :=
  ∃ state pre lower state',
    lower? results state expr = some (pre, lower, state')

def Supported1 (expr : AstExpr) : Prop :=
  Supported 1 expr

def Supported0 (expr : AstExpr) : Prop :=
  Supported 0 expr

namespace List

def SupportedSeq (results : Nat) (exprs : List AstExpr) : Prop :=
  ∃ state pre lowerList state',
    ∃ lowerSeq : Locals.ExprSeq results,
      lowerBound1? state exprs = some (pre, lowerList, state') ∧
        toStackSeq? lowerList results = some lowerSeq

inductive Supported1 : List AstExpr → Prop where
  | nil : Supported1 []
  | cons {expr : AstExpr} {rest : List AstExpr}
      (hExpr : Expr.Supported1 expr)
      (hRest : Supported1 rest) :
      Supported1 (expr :: rest)

end List

mutual
  def names : AstExpr → List Name
    | .Lit _value => []
    | .Var name => [identName name]
    | .Call (.inl _prim) args => List.names args
    | .Call (.inr functionName) args => functionName :: List.names args

  def List.names : List AstExpr → List Name
    | [] => []
    | expr :: rest => names expr ++ List.names rest
end

noncomputable def supported? (results : Nat) (expr : AstExpr) : Bool :=
  match lower? results (Fresh.initial (names expr)) expr with
  | some _ => true
  | none => false

theorem supported_of_check {results : Nat} {expr : AstExpr}
    (hCheck : supported? results expr = true) :
    Supported results expr := by
  unfold supported? at hCheck
  cases hLower : lower? results (Fresh.initial (names expr)) expr with
  | none =>
      simp [hLower] at hCheck
  | some lowered =>
      rcases lowered with ⟨pre, lower, state'⟩
      exact ⟨Fresh.initial (names expr), pre, lower, state', hLower⟩

namespace List

noncomputable def supportedSeq? (results : Nat)
    (exprs : List AstExpr) : Bool :=
  match lowerBound1? (Fresh.initial (Expr.List.names exprs)) exprs with
  | some (_pre, lowerList, _state') =>
      match toStackSeq? lowerList results with
      | some _ => true
      | none => false
  | none => false

theorem supportedSeq_of_check {results : Nat} {exprs : List AstExpr}
    (hCheck : supportedSeq? results exprs = true) :
    SupportedSeq results exprs := by
  unfold supportedSeq? at hCheck
  cases hLower :
      lowerBound1? (Fresh.initial (Expr.List.names exprs)) exprs with
  | none =>
      simp [hLower] at hCheck
  | some lowered =>
      rcases lowered with ⟨pre, lowerList, state'⟩
      cases hSeq : toStackSeq? lowerList results with
      | none =>
          simp [hLower, hSeq] at hCheck
      | some lowerSeq =>
          exact
            ⟨Fresh.initial (Expr.List.names exprs), pre, lowerList, state',
              lowerSeq, hLower, hSeq⟩

noncomputable def supported1? : List AstExpr → Bool
  | [] => true
  | expr :: rest => Expr.supported? 1 expr && supported1? rest

theorem supported1_of_check {exprs : List AstExpr}
    (hCheck : supported1? exprs = true) :
    Supported1 exprs := by
  induction exprs with
  | nil =>
      exact Supported1.nil
  | cons expr rest ih =>
      have hAnd :
          Expr.supported? 1 expr = true ∧ supported1? rest = true := by
        simpa [supported1?] using hCheck
      exact
        Supported1.cons (Expr.supported_of_check hAnd.1)
          (ih hAnd.2)

end List

abbrev AliasEnv := List (Name × AstExpr)

namespace AliasEnv

def lookup? (name : Name) : AliasEnv → Option AstExpr
  | [] => none
  | (candidate, value) :: rest =>
      if candidate = name then
        some value
      else
        lookup? name rest

def erase (name : Name) : AliasEnv → AliasEnv
  | [] => []
  | (candidate, value) :: rest =>
      if candidate = name then
        erase name rest
      else
        (candidate, value) :: erase name rest

def eraseMany (names : List Name) (env : AliasEnv) : AliasEnv :=
  names.foldl (fun acc name => erase name acc) env

def insert (name : Name) (value : AstExpr) (env : AliasEnv) : AliasEnv :=
  (name, value) :: erase name env

end AliasEnv

mutual
  def substAliases (env : AliasEnv) : AstExpr → AstExpr
    | .Lit value => .Lit value
    | .Var name =>
        match AliasEnv.lookup? (identName name) env with
        | some value => value
        | none => .Var name
    | .Call kind args => .Call kind (List.substAliases env args)

  def List.substAliases (env : AliasEnv) : List AstExpr → List AstExpr
    | [] => []
    | expr :: rest => substAliases env expr :: List.substAliases env rest
end

mutual
  def safeAlias? (assigned : List Name) : AstExpr → Option AstExpr
    | .Lit value => some (.Lit value)
    | .Var source =>
        if assigned.contains (identName source) then
          none
        else
          some (.Var source)
    | .Call (.inl prim) args =>
        if pureAliasPrim? prim then do
          let args' ← List.safeAlias? assigned args
          some (.Call (.inl prim) args')
        else
          none
    | .Call (.inr _functionName) _args => none

  def List.safeAlias? (assigned : List Name) :
      List AstExpr → Option (List AstExpr)
    | [] => some []
    | expr :: rest => do
        let head ← safeAlias? assigned expr
        let tail ← List.safeAlias? assigned rest
        some (head :: tail)
end

def simpleAlias? (assigned : List Name) (name : Name)
    (value : AstExpr) : Option AstExpr :=
  if assigned.contains name then
    none
  else
    safeAlias? assigned value

end Expr

namespace Stmt

def zero : Word :=
  EvmYul.UInt256.ofNat 0

def initNames (names : List Name) : List Functions.Stmt :=
  names.map fun name => Functions.Stmt.let_ name (.lit zero)

def letFromTemps : List Name → List Name → Option (List Functions.Stmt)
  | [], [] => some []
  | name :: names, tmp :: tmps => do
      let rest ← letFromTemps names tmps
      some (Functions.Stmt.let_ name (.var tmp) :: rest)
  | _, _ => none

mutual
  def names : AstStmt → List Name
    | .Block body => List.names body
    | .Let vars none => identNames vars
    | .Let vars (some expr) => identNames vars ++ Expr.names expr
    | .Assign vars expr => identNames vars ++ Expr.names expr
    | .ExprStmtCall expr => Expr.names expr
    | .Switch scrutinee cases defaultBody =>
        Expr.names scrutinee ++ CaseList.names cases ++ List.names defaultBody
    | .For cond post body =>
        Expr.names cond ++ List.names post ++ List.names body
    | .If cond body =>
        Expr.names cond ++ List.names body
    | .Continue | .Break | .Leave => []

  def List.names : List AstStmt → List Name
    | [] => []
    | stmt :: rest => names stmt ++ List.names rest

  def CaseList.names : List (Word × List AstStmt) → List Name
    | [] => []
    | (_value, body) :: rest => List.names body ++ CaseList.names rest
end

mutual
  def assignedNames : AstStmt → List Name
    | .Block body => List.assignedNames body
    | .Let _vars _value => []
    | .Assign vars _expr => identNames vars
    | .ExprStmtCall _expr => []
    | .Switch _scrutinee cases defaultBody =>
        CaseList.assignedNames cases ++ List.assignedNames defaultBody
    | .For _cond post body =>
        List.assignedNames post ++ List.assignedNames body
    | .If _cond body =>
        List.assignedNames body
    | .Continue | .Break | .Leave => []

  def List.assignedNames : List AstStmt → List Name
    | [] => []
    | stmt :: rest => assignedNames stmt ++ List.assignedNames rest

  def CaseList.assignedNames : List (Word × List AstStmt) → List Name
    | [] => []
    | (_value, body) :: rest =>
        List.assignedNames body ++ CaseList.assignedNames rest
end

mutual
  def touchNames : AstStmt → List Name
    | .Block body => List.touchNames body
    | .Let _vars none => []
    | .Let _vars (some expr) => Expr.names expr
    | .Assign vars expr => identNames vars ++ Expr.names expr
    | .ExprStmtCall expr => Expr.names expr
    | .Switch scrutinee cases defaultBody =>
        Expr.names scrutinee ++
          CaseList.touchNames cases ++ List.touchNames defaultBody
    | .For cond post body =>
        Expr.names cond ++ List.touchNames post ++ List.touchNames body
    | .If cond body =>
        Expr.names cond ++ List.touchNames body
    | .Continue | .Break | .Leave => []

  def List.touchNames : List AstStmt → List Name
    | [] => []
    | stmt :: rest => touchNames stmt ++ List.touchNames rest

  def CaseList.touchNames : List (Word × List AstStmt) → List Name
    | [] => []
    | (_value, body) :: rest =>
        List.touchNames body ++ CaseList.touchNames rest
end

mutual
  def declaredNames : AstStmt → List Name
    | .Block body => List.declaredNames body
    | .Let vars _value => identNames vars
    | .Assign _vars _expr => []
    | .ExprStmtCall _expr => []
    | .Switch _scrutinee cases defaultBody =>
        CaseList.declaredNames cases ++ List.declaredNames defaultBody
    | .For _cond post body =>
        List.declaredNames post ++ List.declaredNames body
    | .If _cond body =>
        List.declaredNames body
    | .Continue | .Break | .Leave => []

  def List.declaredNames : List AstStmt → List Name
    | [] => []
    | stmt :: rest => declaredNames stmt ++ List.declaredNames rest

  def CaseList.declaredNames : List (Word × List AstStmt) → List Name
    | [] => []
    | (_value, body) :: rest =>
        List.declaredNames body ++ CaseList.declaredNames rest
end

mutual
  def fuel : AstStmt → Nat
    | .Block body => List.fuel body + 2
    | .Let _vars _value => 2
    | .Assign _vars _value => 2
    | .ExprStmtCall _expr => 2
    | .Switch _scrutinee cases defaultBody =>
        Nat.max (CaseList.fuel cases) (List.fuel defaultBody) + 2
    | .For _cond post body =>
        Nat.max (List.fuel post) (List.fuel body) + 2
    | .If _cond body => List.fuel body + 2
    | .Continue | .Break | .Leave => 2

  def List.fuel : List AstStmt → Nat
    | [] => 2
    | stmt :: rest => Nat.max (fuel stmt) (List.fuel rest) + 2

  def CaseList.fuel : List (Word × List AstStmt) → Nat
    | [] => 2
    | (_value, body) :: rest =>
        Nat.max (List.fuel body) (CaseList.fuel rest) + 2
end

def clearAliases (vars : List EvmYul.Identifier)
    (env : Expr.AliasEnv) : Expr.AliasEnv :=
  Expr.AliasEnv.eraseMany (identNames vars) env

mutual
  def simplifyAliasesStmt (assigned : List Name) (env : Expr.AliasEnv) :
      AstStmt → AstStmt × Expr.AliasEnv
    | .Block body =>
        let body' := List.simplifyAliasesWithEnv assigned env body
        (.Block body', env)
    | .Let [name] (some value) =>
        let value' := Expr.substAliases env value
        match Expr.simpleAlias? assigned (identName name) value' with
        | some aliasedValue =>
            (.Block [], Expr.AliasEnv.insert (identName name) aliasedValue env)
        | none =>
            (.Let [name] (some value'), clearAliases [name] env)
    | .Let vars none =>
        (.Let vars none, clearAliases vars env)
    | .Let vars (some value) =>
        let value' := Expr.substAliases env value
        (.Let vars (some value'), clearAliases vars env)
    | .Assign vars value =>
        let value' := Expr.substAliases env value
        (.Assign vars value', clearAliases vars env)
    | .ExprStmtCall expr =>
        (.ExprStmtCall (Expr.substAliases env expr), env)
    | .Switch scrutinee cases defaultBody =>
        let scrutinee' := Expr.substAliases env scrutinee
        let cases' := CaseList.simplifyAliasesWithEnv assigned env cases
        let defaultBody' := List.simplifyAliasesWithEnv assigned env defaultBody
        (.Switch scrutinee' cases' defaultBody', env)
    | .For cond post body =>
        let cond' := Expr.substAliases env cond
        let post' := List.simplifyAliasesWithEnv assigned env post
        let body' := List.simplifyAliasesWithEnv assigned env body
        (.For cond' post' body', env)
    | .If cond body =>
        let cond' := Expr.substAliases env cond
        let body' := List.simplifyAliasesWithEnv assigned env body
        (.If cond' body', env)
    | .Continue => (.Continue, env)
    | .Break => (.Break, env)
    | .Leave => (.Leave, env)

  def List.simplifyAliasesAux (assigned : List Name) :
      Expr.AliasEnv → List AstStmt → List AstStmt × Expr.AliasEnv
    | env, [] => ([], env)
    | env, stmt :: rest =>
        let (stmt', env') := simplifyAliasesStmt assigned env stmt
        let (rest', env'') := List.simplifyAliasesAux assigned env' rest
        match stmt' with
        | .Block [] => (rest', env'')
        | _ => (stmt' :: rest', env'')

  def List.simplifyAliasesWithEnv (assigned : List Name)
      (env : Expr.AliasEnv) (stmts : List AstStmt) : List AstStmt :=
    (List.simplifyAliasesAux assigned env stmts).1

  def CaseList.simplifyAliasesWithEnv (assigned : List Name)
      (env : Expr.AliasEnv) :
      List (Word × List AstStmt) → List (Word × List AstStmt)
    | [] => []
    | (value, body) :: rest =>
        (value, List.simplifyAliasesWithEnv assigned env body) ::
          CaseList.simplifyAliasesWithEnv assigned env rest
end

def List.simplifyAliases (stmts : List AstStmt) : List AstStmt :=
  List.simplifyAliasesWithEnv (List.assignedNames stmts) [] stmts

def anyNameIn (needles haystack : List Name) : Bool :=
  needles.any fun name => haystack.contains name

def letNames : AstStmt → Option (List EvmYul.Identifier)
  | .Let vars _value => some vars
  | _ => none

def splitAfterLastTouch (names : List Name) :
    List AstStmt → List AstStmt × List AstStmt
  | [] => ([], [])
  | stmt :: rest =>
      let (inside, outside) := splitAfterLastTouch names rest
      if anyNameIn names (touchNames stmt) then
        (stmt :: inside, outside)
      else
        match inside with
        | [] => ([], stmt :: outside)
        | _ => (stmt :: inside, outside)

def List.scopeLetLifetimesMappedFuel :
    Nat → List AstStmt → List AstStmt
  | 0, stmts => stmts
  | _fuel + 1, [] => []
  | fuel + 1, stmt :: rest =>
      match letNames stmt with
      | some vars =>
          let names := identNames vars
          let (inside, outside) := splitAfterLastTouch names rest
          let declaredInside := List.declaredNames inside
          let outsideTouches := List.touchNames outside
          if anyNameIn declaredInside outsideTouches then
            stmt :: List.scopeLetLifetimesMappedFuel fuel rest
          else
            .Block (stmt :: List.scopeLetLifetimesMappedFuel fuel inside) ::
              List.scopeLetLifetimesMappedFuel fuel outside
      | none =>
          stmt :: List.scopeLetLifetimesMappedFuel fuel rest

mutual
  def scopeLetLifetimesStmt : AstStmt → AstStmt
    | .Block body => .Block (List.scopeLetLifetimes body)
    | .Switch scrutinee cases defaultBody =>
        .Switch scrutinee (CaseList.scopeLetLifetimes cases)
          (List.scopeLetLifetimes defaultBody)
    | .For cond post body =>
        .For cond (List.scopeLetLifetimes post) (List.scopeLetLifetimes body)
    | .If cond body =>
        .If cond (List.scopeLetLifetimes body)
    | stmt => stmt

  def List.scopeLetLifetimes (stmts : List AstStmt) : List AstStmt :=
    let mapped := stmts.map scopeLetLifetimesStmt
    List.scopeLetLifetimesMappedFuel (mapped.length + 1) mapped

  def CaseList.scopeLetLifetimes :
      List (Word × List AstStmt) → List (Word × List AstStmt)
    | [] => []
    | (value, body) :: rest =>
        (value, List.scopeLetLifetimes body) ::
          CaseList.scopeLetLifetimes rest
end

def List.simplifyForUnchecked (stmts : List AstStmt) : List AstStmt :=
  List.scopeLetLifetimes (List.simplifyAliases stmts)

mutual
  def toFunctionsListFuel? :
      Nat → Fresh.State → AstStmt →
        Option (List Functions.Stmt × Fresh.State)
    | 0, _state, _stmt => none
    | fuel + 1, state, .Block body => do
        let (lower, state') ← List.toBlockFuel? fuel state body
        some ([Functions.Stmt.block lower], state')
    | _fuel + 1, state, .Let names none =>
        some (initNames (identNames names), state)
    | _fuel + 1, state, .Let [] (some (.Call (.inr functionName) args)) =>
        if ObjectBuiltin.unsupported? functionName then
          none
        else do
          let (preArgs, lowerArgs, state') ←
            if Expr.List.directCallArgsSafe? args then do
              let lowerArgs ← Expr.List.toLocals1? args
              some ([], lowerArgs, state)
            else
              Expr.List.lowerBound1? state args
          some
            (preArgs ++ [Functions.Stmt.call [] functionName lowerArgs],
              state')
    | _fuel + 1, state, .Let [name] (some (.Call (.inr functionName) args)) =>
        if ObjectBuiltin.unsupported? functionName then
          none
        else do
          let lowerNames := identNames [name]
          let (preArgs, lowerArgs, state') ←
            if Expr.List.directCallArgsSafe? args then do
              let lowerArgs ← Expr.List.toLocals1? args
              some ([], lowerArgs, state)
            else
              Expr.List.lowerBound1? state args
          some
            (initNames lowerNames ++ preArgs ++
              [Functions.Stmt.call lowerNames functionName lowerArgs],
              state')
    | _fuel + 1, state, .Let [name] (some value) => do
        let (preValue, lowerValue, state') ← Expr.lower1? state value
        let lowerName := identName name
        some (preValue ++ [Functions.Stmt.let_ lowerName lowerValue], state')
    | _fuel + 1, state,
        .Let (name :: next :: rest) (some (.Call (.inr functionName) args)) =>
        if ObjectBuiltin.unsupported? functionName then
          none
        else do
          let lowerNames := identNames (name :: next :: rest)
          let (preArgs, lowerArgs, state') ←
            if Expr.List.directCallArgsSafe? args then do
              let lowerArgs ← Expr.List.toLocals1? args
              some ([], lowerArgs, state)
            else
              Expr.List.lowerBound1? state args
          -- Multi-result calls declare their visible return slots directly.
          some
            (initNames lowerNames ++ preArgs ++
              [Functions.Stmt.call lowerNames functionName lowerArgs],
              state')
    | _fuel + 1, _state, .Let _names (some _value) =>
        none
    | _fuel + 1, state, .Assign [] (.Call (.inr functionName) args) =>
        if ObjectBuiltin.unsupported? functionName then
          none
        else do
          let (preArgs, lowerArgs, state') ←
            if Expr.List.directCallArgsSafe? args then do
              let lowerArgs ← Expr.List.toLocals1? args
              some ([], lowerArgs, state)
            else
              Expr.List.lowerBound1? state args
          some (preArgs ++ [Functions.Stmt.call [] functionName lowerArgs],
            state')
    | _fuel + 1, state, .Assign [name] (.Call (.inr functionName) args) =>
        if ObjectBuiltin.unsupported? functionName then
          none
        else do
          let lowerNames := identNames [name]
          let (preArgs, lowerArgs, state') ←
            if Expr.List.directCallArgsSafe? args then do
              let lowerArgs ← Expr.List.toLocals1? args
              some ([], lowerArgs, state)
            else
              Expr.List.lowerBound1? state args
          some (preArgs ++ [Functions.Stmt.call lowerNames functionName lowerArgs],
            state')
    | _fuel + 1, state, .Assign [name] value => do
        let (preValue, lowerValue, state') ← Expr.lower1? state value
        some (preValue ++ [Functions.Stmt.assign (identName name) lowerValue],
          state')
    | _fuel + 1, state,
        .Assign (name :: next :: rest) (.Call (.inr functionName) args) =>
        if ObjectBuiltin.unsupported? functionName then
          none
        else do
          let lowerNames := identNames (name :: next :: rest)
          let (preArgs, lowerArgs, state') ←
            if Expr.List.directCallArgsSafe? args then do
              let lowerArgs ← Expr.List.toLocals1? args
              some ([], lowerArgs, state)
            else
              Expr.List.lowerBound1? state args
          some (preArgs ++ [Functions.Stmt.call lowerNames functionName lowerArgs],
            state')
    | _fuel + 1, _state, .Assign _names _value =>
        none
    | _fuel + 1, state, .ExprStmtCall (.Call (.inr functionName) args) =>
        if ObjectBuiltin.unsupported? functionName then
          none
        else do
          let (preArgs, lowerArgs, state') ←
            if Expr.List.directCallArgsSafe? args then do
              let lowerArgs ← Expr.List.toLocals1? args
              some ([], lowerArgs, state)
            else
              Expr.List.lowerBound1? state args
          some (preArgs ++ [Functions.Stmt.call [] functionName lowerArgs],
            state')
    | _fuel + 1, state, .ExprStmtCall (.Call (.inl prim) args) =>
        match Prim.terminal? prim with
        | some kind => do
            let (preArgs, lowerArgs, state') ← Expr.List.lowerBound1? state args
            let seq ← Expr.List.toStackSeq? lowerArgs kind.argCount
            some (preArgs ++ [Functions.Stmt.terminalArgs kind seq], state')
        | none => do
            let (pre, lower, state') ←
              Expr.lower0? state (.Call (.inl prim) args)
            some (pre ++ [Functions.Stmt.expr lower], state')
    | _fuel + 1, state, .ExprStmtCall expr => do
        let (pre, lower, state') ← Expr.lower0? state expr
        some (pre ++ [Functions.Stmt.expr lower], state')
    | fuel + 1, state, .Switch scrutinee cases defaultBody => do
        let (preScrutinee, lowerScrutinee, state') ←
          Expr.lower1? state scrutinee
        let (lowerCases, state'') ← CaseList.toFunctionsFuel? fuel state' cases
        let (lowerDefault, state''') ←
          match defaultBody with
          | [] => some (none, state'')
          | _ => do
              let (body, stateDefault) ← List.toBlockFuel? fuel state'' defaultBody
              some (some body, stateDefault)
        some
          (preScrutinee ++
            [Functions.Stmt.switch lowerScrutinee lowerCases lowerDefault],
            state''')
    | fuel + 1, state, .For cond post body => do
        let (preCond, lowerCond, state') ← Expr.lower1? state cond
        let (lowerPost, state'') ← List.toBlockFuel? fuel state' post
        let (lowerBody, state''') ← List.toBlockFuel? fuel state'' body
        let bodyWithCond : Functions.Block :=
          { stmts :=
              preCond ++
                [Functions.Stmt.if_
                  (.prim .iszero (Locals.ExprSeq.cons lowerCond .nil))
                  { stmts := [Functions.Stmt.brk] }] ++
                lowerBody.stmts }
        some
          ([Functions.Stmt.for_ { stmts := [] } (.lit (EvmYul.UInt256.ofNat 1))
            lowerPost bodyWithCond],
            state''')
    | fuel + 1, state, .If cond body => do
        let (preCond, lowerCond, state') ← Expr.lower1? state cond
        let (lowerBody, state'') ← List.toBlockFuel? fuel state' body
        some (preCond ++ [Functions.Stmt.if_ lowerCond lowerBody], state'')
    | _fuel + 1, state, .Continue =>
        some ([.cont], state)
    | _fuel + 1, state, .Break =>
        some ([.brk], state)
    | _fuel + 1, state, .Leave =>
        some ([.leave], state)

  def List.toFunctionsFuel? :
      Nat → Fresh.State → List AstStmt →
        Option (List Functions.Stmt × Fresh.State)
    | 0, _state, _stmts => none
    | _fuel + 1, state, [] => some ([], state)
    | fuel + 1, state, stmt :: rest => do
        let (lowerStmt, state') ← toFunctionsListFuel? fuel state stmt
        let (lowerRest, state'') ← List.toFunctionsFuel? fuel state' rest
        some (lowerStmt ++ lowerRest, state'')

  def CaseList.toFunctionsFuel? :
      Nat → Fresh.State → List (Word × List AstStmt) →
        Option (List (Word × Functions.Block) × Fresh.State)
    | 0, _state, _cases => none
    | _fuel + 1, state, [] => some ([], state)
    | fuel + 1, state, (value, body) :: rest => do
        let (lowerBody, state') ← List.toBlockFuel? fuel state body
        let (lowerRest, state'') ← CaseList.toFunctionsFuel? fuel state' rest
        some ((value, lowerBody) :: lowerRest, state'')

  def List.toBlockFuel? :
      Nat → Fresh.State → List AstStmt →
        Option (Functions.Block × Fresh.State)
    | 0, _state, _stmts => none
    | fuel + 1, state, stmts => do
        let (lower, state') ← List.toFunctionsFuel? fuel state stmts
        some ({ stmts := lower }, state')
end

mutual
  def toFunctionsListUncheckedFuel? :
      Nat → Fresh.State → AstStmt →
        Option (List Functions.Stmt × Fresh.State)
    | 0, _state, _stmt => none
    | fuel + 1, state, .Block body => do
        let (lower, state') ← List.toBlockUncheckedFuel? fuel state body
        some ([Functions.Stmt.block lower], state')
    | _fuel + 1, state, .Let names none =>
        some (initNames (identNames names), state)
    | _fuel + 1, state, .Let [] (some (.Call (.inr functionName) args)) =>
        if ObjectBuiltin.unsupported? functionName then
          none
        else do
          let (preArgs, lowerArgs, state') ←
            if Expr.List.directCallArgsSafe? args then do
              let lowerArgs ← Expr.List.toLocals1? args
              some ([], lowerArgs, state)
            else
              Expr.List.lowerBound1Unchecked? state args
          some
            (preArgs ++ [Functions.Stmt.call [] functionName lowerArgs],
              state')
    | _fuel + 1, state, .Let [name] (some (.Call (.inr functionName) args)) =>
        if ObjectBuiltin.unsupported? functionName then
          none
        else do
          let lowerNames := identNames [name]
          let (preArgs, lowerArgs, state') ←
            if Expr.List.directCallArgsSafe? args then do
              let lowerArgs ← Expr.List.toLocals1? args
              some ([], lowerArgs, state)
            else
              Expr.List.lowerBound1Unchecked? state args
          some
            (initNames lowerNames ++ preArgs ++
              [Functions.Stmt.call lowerNames functionName lowerArgs],
              state')
    | _fuel + 1, state, .Let [name] (some value) => do
        let (preValue, lowerValue, state') ← Expr.lower1Unchecked? state value
        some (preValue ++ [Functions.Stmt.let_ (identName name) lowerValue],
          state')
    | _fuel + 1, state,
        .Let (name :: next :: rest) (some (.Call (.inr functionName) args)) =>
        if ObjectBuiltin.unsupported? functionName then
          none
        else do
          let lowerNames := identNames (name :: next :: rest)
          let (preArgs, lowerArgs, state') ←
            if Expr.List.directCallArgsSafe? args then do
              let lowerArgs ← Expr.List.toLocals1? args
              some ([], lowerArgs, state)
            else
              Expr.List.lowerBound1Unchecked? state args
          some
            (initNames lowerNames ++ preArgs ++
              [Functions.Stmt.call lowerNames functionName lowerArgs],
              state')
    | _fuel + 1, _state, .Let _names (some _value) =>
        none
    | _fuel + 1, state, .Assign [] (.Call (.inr functionName) args) =>
        if ObjectBuiltin.unsupported? functionName then
          none
        else do
          let (preArgs, lowerArgs, state') ←
            if Expr.List.directCallArgsSafe? args then do
              let lowerArgs ← Expr.List.toLocals1? args
              some ([], lowerArgs, state)
            else
              Expr.List.lowerBound1Unchecked? state args
          some (preArgs ++ [Functions.Stmt.call [] functionName lowerArgs],
            state')
    | _fuel + 1, state, .Assign [name] (.Call (.inr functionName) args) =>
        if ObjectBuiltin.unsupported? functionName then
          none
        else do
          let lowerNames := identNames [name]
          let (preArgs, lowerArgs, state') ←
            if Expr.List.directCallArgsSafe? args then do
              let lowerArgs ← Expr.List.toLocals1? args
              some ([], lowerArgs, state)
            else
              Expr.List.lowerBound1Unchecked? state args
          some (preArgs ++ [Functions.Stmt.call lowerNames functionName lowerArgs],
            state')
    | _fuel + 1, state, .Assign [name] value => do
        let (preValue, lowerValue, state') ← Expr.lower1Unchecked? state value
        some (preValue ++ [Functions.Stmt.assign (identName name) lowerValue],
          state')
    | _fuel + 1, state,
        .Assign (name :: next :: rest) (.Call (.inr functionName) args) =>
        if ObjectBuiltin.unsupported? functionName then
          none
        else do
          let lowerNames := identNames (name :: next :: rest)
          let (preArgs, lowerArgs, state') ←
            if Expr.List.directCallArgsSafe? args then do
              let lowerArgs ← Expr.List.toLocals1? args
              some ([], lowerArgs, state)
            else
              Expr.List.lowerBound1Unchecked? state args
          some (preArgs ++ [Functions.Stmt.call lowerNames functionName lowerArgs],
            state')
    | _fuel + 1, _state, .Assign _names _value =>
        none
    | _fuel + 1, state, .ExprStmtCall (.Call (.inr functionName) args) =>
        if ObjectBuiltin.unsupported? functionName then
          none
        else do
          let (preArgs, lowerArgs, state') ←
            if Expr.List.directCallArgsSafe? args then do
              let lowerArgs ← Expr.List.toLocals1? args
              some ([], lowerArgs, state)
            else
              Expr.List.lowerBound1Unchecked? state args
          some (preArgs ++ [Functions.Stmt.call [] functionName lowerArgs],
            state')
    | _fuel + 1, state, .ExprStmtCall (.Call (.inl prim) args) =>
        match Prim.terminal? prim with
        | some kind => do
            let (preArgs, lowerArgs, state') ←
              Expr.List.lowerBound1Unchecked? state args
            let seq ← Expr.List.toStackSeq? lowerArgs kind.argCount
            some (preArgs ++ [Functions.Stmt.terminalArgs kind seq], state')
        | none => do
            let (pre, lower, state') ←
              Expr.lower0Unchecked? state (.Call (.inl prim) args)
            some (pre ++ [Functions.Stmt.expr lower], state')
    | _fuel + 1, state, .ExprStmtCall expr => do
        let (pre, lower, state') ← Expr.lower0Unchecked? state expr
        some (pre ++ [Functions.Stmt.expr lower], state')
    | fuel + 1, state, .Switch scrutinee cases defaultBody => do
        let (preScrutinee, lowerScrutinee, state') ←
          Expr.lower1Unchecked? state scrutinee
        let (lowerCases, state'') ←
          CaseList.toFunctionsUncheckedFuel? fuel state' cases
        let (lowerDefault, state''') ←
          match defaultBody with
          | [] => some (none, state'')
          | _ => do
              let (body, stateDefault) ←
                List.toBlockUncheckedFuel? fuel state'' defaultBody
              some (some body, stateDefault)
        some
          (preScrutinee ++
            [Functions.Stmt.switch lowerScrutinee lowerCases lowerDefault],
            state''')
    | fuel + 1, state, .For cond post body => do
        let (preCond, lowerCond, state') ← Expr.lower1Unchecked? state cond
        let (lowerPost, state'') ← List.toBlockUncheckedFuel? fuel state' post
        let (lowerBody, state''') ← List.toBlockUncheckedFuel? fuel state'' body
        let bodyWithCond : Functions.Block :=
          { stmts :=
              preCond ++
                [Functions.Stmt.if_
                  (.prim .iszero (Locals.ExprSeq.cons lowerCond .nil))
                  { stmts := [Functions.Stmt.brk] }] ++
                lowerBody.stmts }
        some
          ([Functions.Stmt.for_ { stmts := [] } (.lit (EvmYul.UInt256.ofNat 1))
            lowerPost bodyWithCond],
            state''')
    | fuel + 1, state, .If cond body => do
        let (preCond, lowerCond, state') ← Expr.lower1Unchecked? state cond
        let (lowerBody, state'') ← List.toBlockUncheckedFuel? fuel state' body
        some (preCond ++ [Functions.Stmt.if_ lowerCond lowerBody], state'')
    | _fuel + 1, state, .Continue =>
        some ([.cont], state)
    | _fuel + 1, state, .Break =>
        some ([.brk], state)
    | _fuel + 1, state, .Leave =>
        some ([.leave], state)

  def List.toFunctionsUncheckedFuel? :
      Nat → Fresh.State → List AstStmt →
        Option (List Functions.Stmt × Fresh.State)
    | 0, _state, _stmts => none
    | _fuel + 1, state, [] => some ([], state)
    | fuel + 1, state, stmt :: rest => do
        let (lowerStmt, state') ← toFunctionsListUncheckedFuel? fuel state stmt
        let (lowerRest, state'') ←
          List.toFunctionsUncheckedFuel? fuel state' rest
        some (lowerStmt ++ lowerRest, state'')

  def CaseList.toFunctionsUncheckedFuel? :
      Nat → Fresh.State → List (Word × List AstStmt) →
        Option (List (Word × Functions.Block) × Fresh.State)
    | 0, _state, _cases => none
    | _fuel + 1, state, [] => some ([], state)
    | fuel + 1, state, (value, body) :: rest => do
        let (lowerBody, state') ← List.toBlockUncheckedFuel? fuel state body
        let (lowerRest, state'') ←
          CaseList.toFunctionsUncheckedFuel? fuel state' rest
        some ((value, lowerBody) :: lowerRest, state'')

  def List.toBlockUncheckedFuel? :
      Nat → Fresh.State → List AstStmt →
        Option (Functions.Block × Fresh.State)
    | 0, _state, _stmts => none
    | fuel + 1, state, stmts => do
        let (lower, state') ← List.toFunctionsUncheckedFuel? fuel state stmts
        some ({ stmts := lower }, state')
end

theorem List.toBlockUncheckedFuel?_parts
    {fuel : Nat} {state final : Fresh.State}
    {stmts : List AstStmt} {lower : Functions.Block}
    (hLower :
      Stmt.List.toBlockUncheckedFuel? fuel state stmts =
        some (lower, final)) :
    ∃ previous lowerStmts,
      fuel = previous + 1 ∧
      Stmt.List.toFunctionsUncheckedFuel? previous state stmts =
        some (lowerStmts, final) ∧
      lower = { stmts := lowerStmts } := by
  cases fuel with
  | zero =>
      simp [Stmt.List.toBlockUncheckedFuel?] at hLower
  | succ previous =>
      cases hStmts :
          Stmt.List.toFunctionsUncheckedFuel? previous state stmts with
      | none =>
          simp [Stmt.List.toBlockUncheckedFuel?, hStmts] at hLower
      | some result =>
          rcases result with ⟨lowerStmts, finalState⟩
          simp [Stmt.List.toBlockUncheckedFuel?, hStmts] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          exact ⟨previous, lowerStmts, rfl, hStmts, rfl⟩

theorem List.toFunctionsUncheckedFuel?_nil_parts
    {fuel : Nat} {state final : Fresh.State}
    {lower : List Functions.Stmt}
    (hLower :
      Stmt.List.toFunctionsUncheckedFuel? fuel state [] =
        some (lower, final)) :
    ∃ previous, fuel = previous + 1 ∧ lower = [] ∧ final = state := by
  cases fuel with
  | zero =>
      simp [Stmt.List.toFunctionsUncheckedFuel?] at hLower
  | succ previous =>
      simp [Stmt.List.toFunctionsUncheckedFuel?] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      exact ⟨previous, rfl, rfl, rfl⟩

theorem List.toFunctionsUncheckedFuel?_cons_parts
    {fuel : Nat} {state final : Fresh.State}
    {stmt : AstStmt} {rest : List AstStmt}
    {lower : List Functions.Stmt}
    (hLower :
      Stmt.List.toFunctionsUncheckedFuel? fuel state (stmt :: rest) =
        some (lower, final)) :
    ∃ previous lowerStmt middle lowerRest,
      fuel = previous + 1 ∧
      Stmt.toFunctionsListUncheckedFuel? previous state stmt =
        some (lowerStmt, middle) ∧
      Stmt.List.toFunctionsUncheckedFuel? previous middle rest =
        some (lowerRest, final) ∧
      lower = lowerStmt ++ lowerRest := by
  cases fuel with
  | zero =>
      simp [Stmt.List.toFunctionsUncheckedFuel?] at hLower
  | succ previous =>
      cases hStmt :
          Stmt.toFunctionsListUncheckedFuel? previous state stmt with
      | none =>
          simp [Stmt.List.toFunctionsUncheckedFuel?, hStmt] at hLower
      | some stmtResult =>
          rcases stmtResult with ⟨lowerStmt, middle⟩
          cases hRest :
              Stmt.List.toFunctionsUncheckedFuel? previous middle rest with
          | none =>
              simp [Stmt.List.toFunctionsUncheckedFuel?,
                hStmt, hRest] at hLower
          | some restResult =>
              rcases restResult with ⟨lowerRest, finalState⟩
              simp [Stmt.List.toFunctionsUncheckedFuel?,
                hStmt, hRest] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              exact
                ⟨previous, lowerStmt, middle, lowerRest,
                  rfl, hStmt, hRest, rfl⟩

theorem List.toBlockUncheckedFuel?_singleton_leave_parts
    {fuel : Nat} {state final : Fresh.State}
    {lower : Functions.Block}
    (hLower :
      List.toBlockUncheckedFuel? fuel state [.Leave] =
        some (lower, final)) :
    lower = { stmts := [.leave] } ∧ final = state := by
  obtain ⟨previous, lowerStmts, _hFuel, hList, hBlock⟩ :=
    List.toBlockUncheckedFuel?_parts hLower
  obtain
      ⟨stmtFuel, lowerStmt, middle, lowerRest,
        _hPrevious, hStmt, hRest, hStmts⟩ :=
    List.toFunctionsUncheckedFuel?_cons_parts hList
  cases stmtFuel with
  | zero =>
      simp [toFunctionsListUncheckedFuel?] at hStmt
  | succ remaining =>
      simp [toFunctionsListUncheckedFuel?] at hStmt
      rcases hStmt with ⟨rfl, rfl⟩
      obtain ⟨_restFuel, _hRestFuel, hLowerRest, hFinal⟩ :=
        List.toFunctionsUncheckedFuel?_nil_parts hRest
      subst lowerRest
      subst final
      constructor
      · simpa [hStmts] using hBlock
      · rfl

theorem toFunctionsListUncheckedFuel?_let_gas
    (fuel : Nat) (state : Fresh.State) (name : EvmYul.Identifier) :
    toFunctionsListUncheckedFuel? fuel.succ state
        (.Let [name]
          (some
            (.Call (.inl
              ((.StackMemFlow .GAS : EvmYul.Operation .Yul))) []))) =
      some
        ([Functions.Stmt.let_ (identName name)
          (.prim .gas .nil : Locals.Expr 1)], state) := by
  simp [toFunctionsListUncheckedFuel?, Expr.lower1Unchecked?_gas]

theorem toFunctionsListUncheckedFuel?_let_msize
    (fuel : Nat) (state : Fresh.State) (name : EvmYul.Identifier) :
    toFunctionsListUncheckedFuel? fuel.succ state
        (.Let [name]
          (some
            (.Call (.inl
              ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul))) []))) =
      some
        ([Functions.Stmt.let_ (identName name)
          (.prim .msize .nil : Locals.Expr 1)], state) := by
  simp [toFunctionsListUncheckedFuel?, Expr.lower1Unchecked?_msize]

theorem toFunctionsListUncheckedFuel?_assign_gas
    (fuel : Nat) (state : Fresh.State) (name : EvmYul.Identifier) :
    toFunctionsListUncheckedFuel? fuel.succ state
        (.Assign [name]
          (.Call (.inl
            ((.StackMemFlow .GAS : EvmYul.Operation .Yul))) [])) =
      some
        ([Functions.Stmt.assign (identName name)
          (.prim .gas .nil : Locals.Expr 1)], state) := by
  simp [toFunctionsListUncheckedFuel?, Expr.lower1Unchecked?_gas]

theorem toFunctionsListUncheckedFuel?_assign_msize
    (fuel : Nat) (state : Fresh.State) (name : EvmYul.Identifier) :
    toFunctionsListUncheckedFuel? fuel.succ state
        (.Assign [name]
          (.Call (.inl
            ((.StackMemFlow .MSIZE : EvmYul.Operation .Yul))) [])) =
      some
        ([Functions.Stmt.assign (identName name)
          (.prim .msize .nil : Locals.Expr 1)], state) := by
  simp [toFunctionsListUncheckedFuel?, Expr.lower1Unchecked?_msize]

noncomputable def toFunctionsList? (state : Fresh.State) (stmt : AstStmt) :
    Option (List Functions.Stmt × Fresh.State) :=
  toFunctionsListFuel? (fuel stmt) state stmt

noncomputable def List.toFunctions? (state : Fresh.State)
    (stmts : List AstStmt) :
    Option (List Functions.Stmt × Fresh.State) :=
  List.toFunctionsFuel? (List.fuel stmts) state stmts

noncomputable def CaseList.toFunctions? (state : Fresh.State)
    (cases : List (Word × List AstStmt)) :
    Option (List (Word × Functions.Block) × Fresh.State) :=
  CaseList.toFunctionsFuel? (CaseList.fuel cases) state cases

noncomputable def List.toBlock? (state : Fresh.State) (stmts : List AstStmt) :
    Option (Functions.Block × Fresh.State) :=
  List.toBlockFuel? (List.fuel stmts) state stmts

mutual
  inductive Supported : AstStmt → Prop where
    | block {body : List AstStmt}
        (hBody : StmtListSupported body) :
        Supported (.Block body)
    | letNone {names : List Name} :
        Supported (.Let names none)
    | letCall {names : List Name} {functionName : Name}
        {args : List AstExpr}
        (hName : ObjectBuiltin.unsupported? functionName = false)
        (hArgs : Expr.List.Supported1 args) :
        Supported (.Let names (some (.Call (.inr functionName) args)))
    | letValue {name : Name} {value : AstExpr}
        (hValue : Expr.Supported1 value) :
        Supported (.Let [name] (some value))
    | assignCall {names : List Name} {functionName : Name}
        {args : List AstExpr}
        (hName : ObjectBuiltin.unsupported? functionName = false)
        (hArgs : Expr.List.Supported1 args) :
        Supported (.Assign names (.Call (.inr functionName) args))
    | assignValue {name : Name} {value : AstExpr}
        (hValue : Expr.Supported1 value) :
        Supported (.Assign [name] value)
    | exprCall {functionName : Name} {args : List AstExpr}
        (hName : ObjectBuiltin.unsupported? functionName = false)
        (hArgs : Expr.List.Supported1 args) :
        Supported (.ExprStmtCall (.Call (.inr functionName) args))
    | terminalPrim {prim : EvmYul.Operation .Yul}
        {kind : Assembly.HaltKind} {args : List AstExpr}
        (hTerminal : Prim.terminal? prim = some kind)
        (hArgs : Expr.List.SupportedSeq kind.argCount args) :
        Supported (.ExprStmtCall (.Call (.inl prim) args))
    | terminalStop {prim : EvmYul.Operation .Yul}
        {kind : Assembly.HaltKind}
        (hStop : Prim.stop? prim = some kind) :
        Supported (.ExprStmtCall (.Call (.inl prim) []))
    | expr {expr : AstExpr}
        (hExpr : Expr.Supported0 expr) :
        Supported (.ExprStmtCall expr)
    | switch {scrutinee : AstExpr}
        {cases : List (Word × List AstStmt)}
        {defaultBody : List AstStmt}
        (hScrutinee : Expr.Supported1 scrutinee)
        (hCases : CaseListSupported cases)
        (hDefault : StmtListSupported defaultBody) :
        Supported (.Switch scrutinee cases defaultBody)
    | for_ {cond : AstExpr} {post body : List AstStmt}
        (hCond : Expr.Supported1 cond)
        (hPost : StmtListSupported post)
        (hBody : StmtListSupported body) :
        Supported (.For cond post body)
    | if_ {cond : AstExpr} {body : List AstStmt}
        (hCond : Expr.Supported1 cond)
        (hBody : StmtListSupported body) :
        Supported (.If cond body)
    | cont :
        Supported .Continue
    | brk :
        Supported .Break
    | leave :
        Supported .Leave

  inductive StmtListSupported : List AstStmt → Prop where
    | nil : StmtListSupported []
    | cons {stmt : AstStmt} {rest : List AstStmt}
        (hStmt : Stmt.Supported stmt)
        (hRest : StmtListSupported rest) :
        StmtListSupported (stmt :: rest)

  inductive CaseListSupported :
      List (Word × List AstStmt) → Prop where
    | nil : CaseListSupported []
    | cons {value : Word} {body : List AstStmt}
        {rest : List (Word × List AstStmt)}
        (hBody : StmtListSupported body)
        (hRest : CaseListSupported rest) :
        CaseListSupported ((value, body) :: rest)
end

mutual
  noncomputable def supported? : AstStmt → Bool
    | .Block body => stmtListSupported? body
    | .Let names value =>
        match value with
        | none => true
        | some (.Call (.inr functionName) args) =>
            if ObjectBuiltin.unsupported? functionName then
              false
            else
              Expr.List.supported1? args
        | some value =>
            match names with
            | [_name] => Expr.supported? 1 value
            | _ => false
    | .Assign names value =>
        match value with
        | .Call (.inr functionName) args =>
            if ObjectBuiltin.unsupported? functionName then
              false
            else
              Expr.List.supported1? args
        | value =>
            match names with
            | [_name] => Expr.supported? 1 value
            | _ => false
    | .ExprStmtCall expr =>
        match expr with
        | .Call (.inr functionName) args =>
            if ObjectBuiltin.unsupported? functionName then
              false
            else
              Expr.List.supported1? args
        | .Call (.inl prim) args =>
            match Prim.terminal? prim with
            | some kind => Expr.List.supportedSeq? kind.argCount args
            | none => Expr.supported? 0 (.Call (.inl prim) args)
        | expr => Expr.supported? 0 expr
    | .Switch scrutinee cases defaultBody =>
        Expr.supported? 1 scrutinee &&
          (caseListSupported? cases && stmtListSupported? defaultBody)
    | .For cond post body =>
        Expr.supported? 1 cond &&
          (stmtListSupported? post && stmtListSupported? body)
    | .If cond body =>
        Expr.supported? 1 cond && stmtListSupported? body
    | .Continue => true
    | .Break => true
    | .Leave => true

  noncomputable def stmtListSupported? : List AstStmt → Bool
    | [] => true
    | stmt :: rest => supported? stmt && stmtListSupported? rest

  noncomputable def caseListSupported? :
      List (Word × List AstStmt) → Bool
    | [] => true
    | (_value, body) :: rest =>
        stmtListSupported? body && caseListSupported? rest
end

mutual
  theorem supported_of_check {stmt : AstStmt}
      (hCheck : supported? stmt = true) :
      Supported stmt := by
    cases stmt with
    | Block body =>
        exact Supported.block (stmtListSupported_of_check hCheck)
    | Let names value =>
        cases value with
        | none =>
            exact Supported.letNone
        | some value =>
            cases value with
            | Call target args =>
                cases target with
                | inl prim =>
                    cases names with
                    | nil =>
                        simp [supported?] at hCheck
                    | cons name rest =>
                        cases rest with
                        | nil =>
                            exact
                              Supported.letValue
                                (Expr.supported_of_check hCheck)
                        | cons next rest =>
                            simp [supported?] at hCheck
                | inr functionName =>
                    cases hName : ObjectBuiltin.unsupported? functionName with
                    | false =>
                        have hArgs :
                            Expr.List.supported1? args = true := by
                          simp [supported?, hName] at hCheck
                          exact hCheck
                        exact
                          Supported.letCall hName
                            (Expr.List.supported1_of_check hArgs)
                    | true =>
                        simp [supported?, hName] at hCheck
            | Lit value =>
                cases names with
                | nil =>
                    simp [supported?] at hCheck
                | cons name rest =>
                    cases rest with
                    | nil =>
                        exact
                          Supported.letValue
                            (Expr.supported_of_check hCheck)
                    | cons next rest =>
                        simp [supported?] at hCheck
            | Var name =>
                cases names with
                | nil =>
                    simp [supported?] at hCheck
                | cons target rest =>
                    cases rest with
                    | nil =>
                        exact
                          Supported.letValue
                            (Expr.supported_of_check hCheck)
                    | cons next rest =>
                        simp [supported?] at hCheck
    | Assign names value =>
        cases value with
        | Call target args =>
            cases target with
            | inl prim =>
                cases names with
                | nil =>
                    simp [supported?] at hCheck
                | cons name rest =>
                    cases rest with
                    | nil =>
                        exact
                          Supported.assignValue
                            (Expr.supported_of_check hCheck)
                    | cons next rest =>
                        simp [supported?] at hCheck
            | inr functionName =>
                cases hName : ObjectBuiltin.unsupported? functionName with
                | false =>
                    have hArgs :
                        Expr.List.supported1? args = true := by
                      simp [supported?, hName] at hCheck
                      exact hCheck
                    exact
                      Supported.assignCall hName
                        (Expr.List.supported1_of_check hArgs)
                | true =>
                    simp [supported?, hName] at hCheck
        | Lit value =>
            cases names with
            | nil =>
                simp [supported?] at hCheck
            | cons name rest =>
                cases rest with
                | nil =>
                    exact
                      Supported.assignValue
                        (Expr.supported_of_check hCheck)
                | cons next rest =>
                    simp [supported?] at hCheck
        | Var name =>
            cases names with
            | nil =>
                simp [supported?] at hCheck
            | cons target rest =>
                cases rest with
                | nil =>
                    exact
                      Supported.assignValue
                        (Expr.supported_of_check hCheck)
                | cons next rest =>
                    simp [supported?] at hCheck
    | ExprStmtCall expr =>
        cases expr with
        | Call target args =>
            cases target with
            | inl prim =>
                cases hTerminal : Prim.terminal? prim with
                | none =>
                    have hExpr :
                        Expr.supported? 0 (.Call (.inl prim) args) =
                          true := by
                      simpa [supported?, hTerminal] using hCheck
                    exact
                      Supported.expr
                        (Expr.supported_of_check hExpr)
                | some kind =>
                    have hArgs :
                        Expr.List.supportedSeq? kind.argCount args =
                          true := by
                      simpa [supported?, hTerminal] using hCheck
                    exact
                      Supported.terminalPrim hTerminal
                        (Expr.List.supportedSeq_of_check hArgs)
            | inr functionName =>
                cases hName : ObjectBuiltin.unsupported? functionName with
                | false =>
                    have hArgs :
                        Expr.List.supported1? args = true := by
                      simp [supported?, hName] at hCheck
                      exact hCheck
                    exact
                      Supported.exprCall hName
                        (Expr.List.supported1_of_check hArgs)
                | true =>
                    simp [supported?, hName] at hCheck
        | Lit value =>
            exact Supported.expr (Expr.supported_of_check hCheck)
        | Var name =>
            exact Supported.expr (Expr.supported_of_check hCheck)
    | Switch scrutinee cases defaultBody =>
        have hHead :
            Expr.supported? 1 scrutinee = true ∧
              (caseListSupported? cases &&
                stmtListSupported? defaultBody) = true := by
          simpa [supported?] using hCheck
        have hTail :
            caseListSupported? cases = true ∧
              stmtListSupported? defaultBody = true := by
          simpa using hHead.2
        exact
          Supported.switch (Expr.supported_of_check hHead.1)
            (caseListSupported_of_check hTail.1)
            (stmtListSupported_of_check hTail.2)
    | For cond post body =>
        have hHead :
            Expr.supported? 1 cond = true ∧
              (stmtListSupported? post && stmtListSupported? body) = true := by
          simpa [supported?] using hCheck
        have hTail :
            stmtListSupported? post = true ∧
              stmtListSupported? body = true := by
          simpa using hHead.2
        exact
          Supported.for_ (Expr.supported_of_check hHead.1)
            (stmtListSupported_of_check hTail.1)
            (stmtListSupported_of_check hTail.2)
    | If cond body =>
        have hAnd :
            Expr.supported? 1 cond = true ∧
              stmtListSupported? body = true := by
          simpa [supported?] using hCheck
        exact
          Supported.if_ (Expr.supported_of_check hAnd.1)
            (stmtListSupported_of_check hAnd.2)
    | Continue =>
        exact Supported.cont
    | Break =>
        exact Supported.brk
    | Leave =>
        exact Supported.leave

  theorem stmtListSupported_of_check {stmts : List AstStmt}
      (hCheck : stmtListSupported? stmts = true) :
      StmtListSupported stmts := by
    cases stmts with
    | nil =>
        exact StmtListSupported.nil
    | cons stmt rest =>
        have hAnd :
            supported? stmt = true ∧ stmtListSupported? rest = true := by
          simpa [stmtListSupported?] using hCheck
        exact
          StmtListSupported.cons (supported_of_check hAnd.1)
            (stmtListSupported_of_check hAnd.2)

  theorem caseListSupported_of_check
      {cases : List (Word × List AstStmt)}
      (hCheck : caseListSupported? cases = true) :
      CaseListSupported cases := by
    cases cases with
    | nil =>
        exact CaseListSupported.nil
    | cons head rest =>
        rcases head with ⟨value, body⟩
        have hAnd :
            stmtListSupported? body = true ∧
              caseListSupported? rest = true := by
          simpa [caseListSupported?] using hCheck
        exact
          CaseListSupported.cons (stmtListSupported_of_check hAnd.1)
            (caseListSupported_of_check hAnd.2)
end

end Stmt

namespace FunctionDefinition

def names : AstFunctionDefinition → List Name
  | .Def params returns body =>
      identNames params ++ identNames returns ++ Stmt.List.names body

def fuel : AstFunctionDefinition → Nat
  | .Def _params _returns body => Stmt.List.fuel body + 2

def toFunDefFuel? (fuel : Nat) (state : Fresh.State) (name : Name) :
    AstFunctionDefinition → Option (Functions.FunDef × Fresh.State)
  | .Def params returns body => do
      let (lowerBody, state') ← Stmt.List.toBlockFuel? fuel state body
      let lowerFn : Functions.FunDef :=
        { name := name
          params := identNames params
          returns := identNames returns
          body := lowerBody }
      some (lowerFn, state')

def toFunDefUncheckedFuel? (fuel : Nat) (state : Fresh.State) (name : Name) :
    AstFunctionDefinition → Option (Functions.FunDef × Fresh.State)
  | .Def params returns body => do
      let (lowerBody, state') ← Stmt.List.toBlockUncheckedFuel? fuel state body
      let lowerFn : Functions.FunDef :=
        { name := name
          params := identNames params
          returns := identNames returns
          body := lowerBody }
      some (lowerFn, state')

theorem toFunDefUncheckedFuel?_name
    {fuel : Nat} {state state' : Fresh.State}
    {name : Name} {fn : AstFunctionDefinition}
    {lower : Functions.FunDef}
    (hLower :
      toFunDefUncheckedFuel? fuel state name fn =
        some (lower, state')) :
    lower.name = name := by
  cases fn with
  | Def params returns body =>
      cases hBody :
          Stmt.List.toBlockUncheckedFuel? fuel state body with
      | none =>
          simp [toFunDefUncheckedFuel?, hBody] at hLower
      | some result =>
          rcases result with ⟨lowerBody, finalState⟩
          simp [toFunDefUncheckedFuel?, hBody] at hLower
          rcases hLower with ⟨rfl, rfl⟩
          rfl

theorem toFunDefUncheckedFuel?_parts
    {fuel : Nat} {state state' : Fresh.State}
    {name : Name} {params returns : List EvmYul.Identifier}
    {body : List AstStmt} {lower : Functions.FunDef}
    (hLower :
      toFunDefUncheckedFuel? fuel state name
          (.Def params returns body) =
        some (lower, state')) :
    lower.name = name ∧
      lower.params = identNames params ∧
      lower.returns = identNames returns ∧
      Stmt.List.toBlockUncheckedFuel? fuel state body =
        some (lower.body, state') := by
  cases hBody :
      Stmt.List.toBlockUncheckedFuel? fuel state body with
  | none =>
      simp [toFunDefUncheckedFuel?, hBody] at hLower
  | some result =>
      rcases result with ⟨lowerBody, finalState⟩
      simp [toFunDefUncheckedFuel?, hBody] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl, rfl, rfl⟩

noncomputable def toFunDef? (state : Fresh.State) (name : Name) :
    AstFunctionDefinition → Option (Functions.FunDef × Fresh.State)
  | fn => toFunDefFuel? (fuel fn) state name fn

def Supported : AstFunctionDefinition → Prop
  | .Def _params _returns body => Stmt.StmtListSupported body

noncomputable def supported? : AstFunctionDefinition → Bool
  | .Def _params _returns body => Stmt.stmtListSupported? body

theorem supported_of_check {fn : AstFunctionDefinition}
    (hCheck : supported? fn = true) :
    Supported fn := by
  cases fn with
  | Def params returns body =>
      exact Stmt.stmtListSupported_of_check hCheck

def simplifyAliases : AstFunctionDefinition → AstFunctionDefinition
  | .Def params returns body =>
      .Def params returns (Stmt.List.simplifyAliases body)

def simplifyForUnchecked : AstFunctionDefinition → AstFunctionDefinition
  | .Def params returns body =>
      .Def params returns (Stmt.List.simplifyForUnchecked body)

end FunctionDefinition

namespace FunctionList

def names : List (Name × AstFunctionDefinition) → List Name
  | [] => []
  | (name, fn) :: rest =>
      name :: FunctionDefinition.names fn ++ names rest

def fuel : List (Name × AstFunctionDefinition) → Nat
  | [] => 2
  | (_name, fn) :: rest =>
      Nat.max (FunctionDefinition.fuel fn) (fuel rest) + 2

def toFunDefsFuel? (fuel : Nat) :
    Fresh.State → List (Name × AstFunctionDefinition) →
      Option (List Functions.FunDef × Fresh.State)
  | state, [] => some ([], state)
  | state, (name, fn) :: rest => do
      let (lowerFn, state') ← FunctionDefinition.toFunDefFuel? fuel state name fn
      let (lowerRest, state'') ← toFunDefsFuel? fuel state' rest
      some (lowerFn :: lowerRest, state'')

def toFunDefsUncheckedFuel? (fuel : Nat) :
    Fresh.State → List (Name × AstFunctionDefinition) →
      Option (List Functions.FunDef × Fresh.State)
  | state, [] => some ([], state)
  | state, (name, fn) :: rest => do
      let (lowerFn, state') ←
        FunctionDefinition.toFunDefUncheckedFuel? fuel state name fn
      let (lowerRest, state'') ← toFunDefsUncheckedFuel? fuel state' rest
      some (lowerFn :: lowerRest, state'')

inductive UncheckedLowering (fuel : Nat) :
    Fresh.State → List (Name × AstFunctionDefinition) →
      List Functions.FunDef → Fresh.State → Prop where
  | nil (state : Fresh.State) :
      UncheckedLowering fuel state [] [] state
  | cons
      {state stateHead stateFinal : Fresh.State}
      {name : Name} {fn : AstFunctionDefinition}
      {rest : List (Name × AstFunctionDefinition)}
      {lowerFn : Functions.FunDef} {lowerRest : List Functions.FunDef}
      (hHead :
        FunctionDefinition.toFunDefUncheckedFuel?
            fuel state name fn =
          some (lowerFn, stateHead))
      (hRest :
        UncheckedLowering fuel stateHead rest lowerRest stateFinal) :
      UncheckedLowering fuel state ((name, fn) :: rest)
        (lowerFn :: lowerRest) stateFinal

namespace UncheckedLowering

theorem to_toFunDefsUncheckedFuel?
    {fuel : Nat} {state state' : Fresh.State}
    {functions : List (Name × AstFunctionDefinition)}
    {lower : List Functions.FunDef}
    (hLowering :
      UncheckedLowering fuel state functions lower state') :
    toFunDefsUncheckedFuel? fuel state functions =
      some (lower, state') := by
  induction hLowering with
  | nil =>
      rfl
  | cons hHead _hRest ih =>
      simp [toFunDefsUncheckedFuel?, hHead, ih]

theorem names
    {fuel : Nat} {state state' : Fresh.State}
    {functions : List (Name × AstFunctionDefinition)}
    {lower : List Functions.FunDef}
    (hLowering :
      UncheckedLowering fuel state functions lower state') :
    lower.map (fun fn => fn.name) = functions.map Prod.fst := by
  induction hLowering with
  | nil =>
      rfl
  | @cons state stateHead stateFinal name fn rest lowerFn lowerRest
      hHead hRest ih =>
      cases fn with
      | Def params returns body =>
          cases hBody :
              Stmt.List.toBlockUncheckedFuel? fuel state body with
          | none =>
              simp [FunctionDefinition.toFunDefUncheckedFuel?, hBody]
                at hHead
          | some bodyResult =>
              rcases bodyResult with ⟨lowerBody, bodyState⟩
              simp [FunctionDefinition.toFunDefUncheckedFuel?, hBody]
                at hHead
              rcases hHead with ⟨rfl, rfl⟩
              simp [ih]

theorem member
    {fuel : Nat} {state state' : Fresh.State}
    {functions : List (Name × AstFunctionDefinition)}
    {lower : List Functions.FunDef}
    (hLowering :
      UncheckedLowering fuel state functions lower state')
    {name : Name} {fn : AstFunctionDefinition}
    (hMem : (name, fn) ∈ functions) :
    ∃ before after lowerFn,
      lowerFn ∈ lower ∧
      FunctionDefinition.toFunDefUncheckedFuel?
          fuel before name fn =
        some (lowerFn, after) := by
  induction hLowering with
  | nil =>
      simp at hMem
  | @cons state stateHead stateFinal headName headFn rest
      lowerHead lowerRest hHead hRest ih =>
      simp only [List.mem_cons, Prod.mk.injEq] at hMem
      rcases hMem with hHere | hTail
      · rcases hHere with ⟨rfl, rfl⟩
        exact ⟨state, stateHead, lowerHead, by simp, hHead⟩
      · obtain ⟨before, after, lowerFn, hLowerMem, hLowerFn⟩ :=
          ih hTail
        exact
          ⟨before, after, lowerFn,
            List.mem_cons_of_mem lowerHead hLowerMem, hLowerFn⟩

theorem find_of_mem
    {fuel : Nat} {state state' : Fresh.State}
    {functions : List (Name × AstFunctionDefinition)}
    {lower : List Functions.FunDef}
    (hLowering :
      UncheckedLowering fuel state functions lower state')
    (hNames : (functions.map Prod.fst).Nodup)
    {name : Name} {fn : AstFunctionDefinition}
    (hMem : (name, fn) ∈ functions) :
    ∃ before after lowerFn,
      Functions.Source.FunList.find? name lower = some lowerFn ∧
      FunctionDefinition.toFunDefUncheckedFuel?
          fuel before name fn =
        some (lowerFn, after) := by
  obtain ⟨before, after, lowerFn, hLowerMem, hLowerFn⟩ :=
    hLowering.member hMem
  have hLowerName : lowerFn.name = name :=
    FunctionDefinition.toFunDefUncheckedFuel?_name hLowerFn
  have hLowerNames : (lower.map fun entry => entry.name).Nodup := by
    rw [hLowering.names]
    exact hNames
  have hFind :
      Functions.Source.FunList.find? lowerFn.name lower =
        some lowerFn :=
    Functions.Source.FunList.find?_eq_some_of_mem_of_names_nodup
      hLowerMem hLowerNames
  exact ⟨before, after, lowerFn, by simpa [hLowerName] using hFind,
    hLowerFn⟩

end UncheckedLowering

theorem uncheckedLowering_of_toFunDefsUncheckedFuel?
    {fuel : Nat} {state state' : Fresh.State}
    {functions : List (Name × AstFunctionDefinition)}
    {lower : List Functions.FunDef}
    (hLower :
      toFunDefsUncheckedFuel? fuel state functions =
        some (lower, state')) :
    UncheckedLowering fuel state functions lower state' := by
  induction functions generalizing state lower state' with
  | nil =>
      simp [toFunDefsUncheckedFuel?] at hLower
      rcases hLower with ⟨rfl, rfl⟩
      exact UncheckedLowering.nil state
  | cons entry rest ih =>
      rcases entry with ⟨name, fn⟩
      cases hHead :
          FunctionDefinition.toFunDefUncheckedFuel?
            fuel state name fn with
      | none =>
          simp [toFunDefsUncheckedFuel?, hHead] at hLower
      | some headResult =>
          rcases headResult with ⟨lowerFn, stateHead⟩
          cases hRest :
              toFunDefsUncheckedFuel? fuel stateHead rest with
          | none =>
              simp [toFunDefsUncheckedFuel?, hHead, hRest] at hLower
          | some restResult =>
              rcases restResult with ⟨lowerRest, stateFinal⟩
              simp [toFunDefsUncheckedFuel?, hHead, hRest] at hLower
              rcases hLower with ⟨rfl, rfl⟩
              exact
                UncheckedLowering.cons hHead (ih hRest)

noncomputable def toFunDefs? :
    Fresh.State → List (Name × AstFunctionDefinition) →
      Option (List Functions.FunDef × Fresh.State)
  | state, functions => toFunDefsFuel? (fuel functions) state functions

def simplifyAliases : List (Name × AstFunctionDefinition) →
    List (Name × AstFunctionDefinition)
  | [] => []
  | (name, fn) :: rest =>
      (name, FunctionDefinition.simplifyAliases fn) :: simplifyAliases rest

def simplifyForUnchecked : List (Name × AstFunctionDefinition) →
    List (Name × AstFunctionDefinition)
  | [] => []
  | (name, fn) :: rest =>
      (name, FunctionDefinition.simplifyForUnchecked fn) ::
        simplifyForUnchecked rest

inductive Supported :
    List (Name × AstFunctionDefinition) → Prop where
  | nil : Supported []
  | cons {name : Name} {fn : AstFunctionDefinition}
      {rest : List (Name × AstFunctionDefinition)}
      (hFn : FunctionDefinition.Supported fn)
      (hRest : Supported rest) :
      Supported ((name, fn) :: rest)

noncomputable def supported? :
    List (Name × AstFunctionDefinition) → Bool
  | [] => true
  | (_name, fn) :: rest =>
      FunctionDefinition.supported? fn && supported? rest

theorem supported_of_check
    {functions : List (Name × AstFunctionDefinition)}
    (hCheck : supported? functions = true) :
    Supported functions := by
  induction functions with
  | nil =>
      exact Supported.nil
  | cons head rest ih =>
      rcases head with ⟨name, fn⟩
      have hAnd :
          FunctionDefinition.supported? fn = true ∧
            supported? rest = true := by
        simpa [supported?] using hCheck
      exact
        Supported.cons (FunctionDefinition.supported_of_check hAnd.1)
          (ih hAnd.2)

end FunctionList

namespace Contract

noncomputable def functionEntries (contract : AstContract) :
    List (Name × AstFunctionDefinition) :=
  contract.functions.keys.toList.filterMap fun name =>
    match contract.functions.lookup name with
    | some fn => some (name, fn)
    | none => none

theorem functionEntries_mem_of_lookup
    {contract : AstContract} {name : Name}
    {fn : AstFunctionDefinition}
    (hLookup : contract.functions.lookup name = some fn) :
    (name, fn) ∈ functionEntries contract := by
  unfold functionEntries
  apply List.mem_filterMap.mpr
  refine ⟨name, ?_, ?_⟩
  · have hMem : name ∈ contract.functions :=
      Finmap.mem_of_lookup_eq_some hLookup
    simpa [Finmap.mem_keys] using hMem
  · simp [hLookup]

theorem functionEntries_names_nodup (contract : AstContract) :
    ((functionEntries contract).map Prod.fst).Nodup := by
  unfold functionEntries
  let emit :=
    fun name =>
      match contract.functions.lookup name with
      | some fn => some (name, fn)
      | none => none
  have hKeys : contract.functions.keys.toList.Nodup :=
    contract.functions.keys.nodup_toList
  change ((contract.functions.keys.toList.filterMap emit).map Prod.fst).Nodup
  generalize contract.functions.keys.toList = keys at hKeys ⊢
  induction keys with
  | nil =>
      simp
  | cons head tail ih =>
      have hNodup := List.nodup_cons.mp hKeys
      cases hLookup : contract.functions.lookup head with
      | none =>
          simp [emit, hLookup]
          exact ih hNodup.2
      | some fn =>
          simp only [List.filterMap_cons, emit, hLookup, Option.toList_some,
            List.flatMap_cons, List.map_cons, List.map_nil,
            List.append_nil]
          apply List.nodup_cons.mpr
          constructor
          · intro hHead
            obtain ⟨entry, hEntryMem, hEntryName⟩ :=
              List.mem_map.mp hHead
            obtain ⟨candidate, hCandidateMem, hCandidate⟩ :=
              List.mem_filterMap.mp hEntryMem
            cases hCandidateLookup :
                contract.functions.lookup candidate with
            | none =>
                simp [emit, hCandidateLookup] at hCandidate
            | some candidateFn =>
                simp [emit, hCandidateLookup] at hCandidate
                rcases hCandidate with ⟨rfl⟩
                simp at hEntryName
                subst candidate
                exact hNodup.1 hCandidateMem
          · exact ih hNodup.2

noncomputable def names (contract : AstContract) : List Name :=
  Stmt.names contract.dispatcher ++ FunctionList.names (functionEntries contract)

noncomputable def toObjects? (contract : AstContract) :
    Option Objects.Program := do
  let initial := Fresh.initial (names contract)
  let (bodyStmts, state) ← Stmt.toFunctionsList? initial contract.dispatcher
  let (functions, _state) ← FunctionList.toFunDefs? state (functionEntries contract)
  let functionProgram : Functions.Program :=
    { functions := functions, body := { stmts := bodyStmts } }
  let root : Objects.Object :=
    .mk "root" functionProgram [] []
  some { root := root }

/--
Observer-admitting contract lowering.

This is the same Yul-to-Objects shape as `toObjects?`, but it uses the
unchecked expression/statement lowerers so visible `gas()` and `msize()` calls
can pass through as `BasicOp.gas`/`BasicOp.msize`.  Its preservation contract is
the explicit observer-oracle route, not the ordinary exact-preservation route.
-/
noncomputable def toObjectsWithObservers? (contract : AstContract) :
    Option Objects.Program := do
  let initial := Fresh.initial (names contract)
  let (bodyStmts, state) ←
    Stmt.toFunctionsListUncheckedFuel? (Stmt.fuel contract.dispatcher)
      initial contract.dispatcher
  let (functions, _state) ←
    FunctionList.toFunDefsUncheckedFuel?
      (FunctionList.fuel (functionEntries contract)) state
      (functionEntries contract)
  let functionProgram : Functions.Program :=
    { functions := functions, body := { stmts := bodyStmts } }
  let root : Objects.Object :=
    .mk "root" functionProgram [] []
  some { root := root }

def Supported (contract : AstContract) : Prop :=
  Stmt.Supported contract.dispatcher ∧
    FunctionList.Supported (functionEntries contract)

noncomputable def supported? (contract : AstContract) : Bool :=
  Stmt.supported? contract.dispatcher &&
    FunctionList.supported? (functionEntries contract)

theorem supported_of_check {contract : AstContract}
    (hCheck : supported? contract = true) :
    Supported contract := by
  have hAnd :
      Stmt.supported? contract.dispatcher = true ∧
        FunctionList.supported? (functionEntries contract) = true := by
    simpa [supported?] using hCheck
  exact
    ⟨Stmt.supported_of_check hAnd.1,
      FunctionList.supported_of_check hAnd.2⟩

end Contract

namespace Program

noncomputable def toObjects? (program : Program) : Option Objects.Program :=
  (Contract.toObjects? program.contract).map fun lower =>
    lower.withMemoryContract program.memoryContract

noncomputable def toExpressions? (program : Program) : Option Expressions.Program := do
  let lower ← toObjects? program
  Objects.Program.toExpressions? lower

abbrev CompileArtifact := Objects.Program.CompileArtifact

noncomputable def compileArtifactWithPolicy?
    (policy : Objects.Program.BackendPolicy) (program : Program) :
    Option CompileArtifact := do
  let lower ← toObjects? program
  Objects.Program.compileArtifactWithPolicy? policy lower

noncomputable def compileArtifact? (program : Program) :
    Option CompileArtifact :=
  compileArtifactWithPolicy? Objects.Program.defaultBackendPolicy program

noncomputable def compile? (program : Program) :
    Option Assembly.TargetProgram := do
  let artifact ← compileArtifact? program
  some artifact.target

noncomputable def toObjectsWithObservers? (program : Program) :
    Option Objects.Program :=
  (Contract.toObjectsWithObservers? program.contract).map fun lower =>
    lower.withMemoryContract program.memoryContract

noncomputable def compileWithObservers? (program : Program) :
    Option Assembly.TargetProgram := do
  let lower ← toObjectsWithObservers? program
  let artifact ← Objects.Program.compileArtifact? lower
  some artifact.target

def WF (program : Program) : Prop :=
  ∀ lower : Objects.Program, toObjects? program = some lower → lower.WF

def Supported (program : Program) : Prop :=
  Contract.Supported program.contract

noncomputable def supported? (program : Program) : Bool :=
  Contract.supported? program.contract

theorem supported_of_check {program : Program}
    (hCheck : supported? program = true) :
    Supported program :=
  Contract.supported_of_check hCheck

def Accepted (program : Program) : Prop :=
  WF program ∧ Supported program ∧
    ∃ lower : Objects.Program,
      toObjects? program = some lower ∧ lower.Accepted

def SourceAccepted (program : Program) : Prop :=
  WF program ∧ Supported program ∧
    ∃ lower : Objects.Program,
      toObjects? program = some lower ∧ lower.SourceAccepted

def SourceAcceptedCore (program : Program) : Prop :=
  ∃ lower : Objects.Program,
    toObjects? program = some lower ∧ lower.SourceAccepted

noncomputable def sourceAcceptedCore? (program : Program) : Bool :=
  match toObjects? program with
  | none => false
  | some lower => Objects.SourceAcceptedCheck.Program.sourceAccepted? lower

theorem sourceAcceptedCore_of_check {program : Program}
    (hCheck : sourceAcceptedCore? program = true) :
    SourceAcceptedCore program := by
  unfold sourceAcceptedCore? at hCheck
  cases hLower : toObjects? program with
  | none =>
      simp [hLower] at hCheck
  | some lower =>
      have hLowerCheck :
          Objects.SourceAcceptedCheck.Program.sourceAccepted? lower = true :=
        by simpa [hLower] using hCheck
      exact
        ⟨lower, hLower,
          Objects.SourceAcceptedCheck.Program.sourceAccepted_of_check
            hLowerCheck⟩

theorem sourceAccepted_of_accepted {program : Program}
    (hAccepted : Accepted program) :
    SourceAccepted program := by
  rcases hAccepted with ⟨hWF, hSupported, lower, hLower, hLowerAccepted⟩
  exact
    ⟨hWF, hSupported, lower, hLower,
      Objects.Program.sourceAccepted_of_accepted hLowerAccepted⟩

theorem sourceAcceptedCore_of_sourceAccepted {program : Program}
    (hSourceAccepted : SourceAccepted program) :
    SourceAcceptedCore program := by
  rcases hSourceAccepted with ⟨_hWF, _hSupported, lower, hLower,
    hLowerSourceAccepted⟩
  exact ⟨lower, hLower, hLowerSourceAccepted⟩

theorem sourceAccepted_of_sourceAcceptedCore_supported {program : Program}
    (hCore : SourceAcceptedCore program)
    (hSupported : Supported program) :
    SourceAccepted program := by
  rcases hCore with ⟨lower, hLower, hLowerSourceAccepted⟩
  have hWF : WF program := by
    intro lower' hLower'
    rw [hLower] at hLower'
    cases hLower'
    exact hLowerSourceAccepted.1
  exact ⟨hWF, hSupported, lower, hLower, hLowerSourceAccepted⟩

theorem toObjects_wf {program : Program} {lower : Objects.Program}
    (hWF : program.WF)
    (hToObjects : program.toObjects? = some lower) :
    lower.WF :=
  hWF lower hToObjects

end Program

end Yul
end EvmCompiler
