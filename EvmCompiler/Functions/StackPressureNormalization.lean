import EvmCompiler.Functions.InteractionSemantics
import EvmCompiler.Locals.InteractionArity
import Mathlib.Data.Nat.Bitwise

/-!
Source-level expression normalization for the checked stack allocator.

This pass changes only pure expression shape. It does not choose physical
stack locations or emit `DUP`/`SWAP`: those remain owned by stack allocation.
The two rewrites preserve source leaf order except for moving a literal across
commutative `AND`, which is silent and state-independent.
-/

namespace EvmCompiler
namespace Functions
namespace StackPressureNormalization

namespace UInt256

def toBitVec (value : EvmYul.UInt256) : BitVec 256 :=
  BitVec.ofNat 256 value.toNat

theorem size_eq_two_pow : EvmYul.UInt256.size = 2^256 := by
  norm_num [EvmYul.UInt256.size]

theorem toBitVec_lor (left right : EvmYul.UInt256) :
    toBitVec (EvmYul.UInt256.lor left right) =
      toBitVec left ||| toBitVec right := by
  rcases left with ⟨left⟩
  rcases right with ⟨right⟩
  have hOr : left.val ||| right.val < 2^256 := by
    have h := (toBitVec ⟨left⟩ ||| toBitVec ⟨right⟩).isLt
    simpa [toBitVec, EvmYul.UInt256.toNat, BitVec.toNat_or,
      BitVec.toNat_ofNat, size_eq_two_pow,
      Nat.mod_eq_of_lt (by simpa [size_eq_two_pow] using left.isLt),
      Nat.mod_eq_of_lt (by simpa [size_eq_two_pow] using right.isLt)] using h
  have hOrSize : left.val ||| right.val < EvmYul.UInt256.size := by
    simpa [size_eq_two_pow] using hOr
  apply BitVec.eq_of_toNat_eq
  simp [toBitVec, EvmYul.UInt256.toNat, EvmYul.UInt256.lor, Fin.lor,
    BitVec.toNat_or, BitVec.toNat_ofNat, size_eq_two_pow]
  exact Nat.mod_eq_of_lt hOrSize

theorem toBitVec_land (left right : EvmYul.UInt256) :
    toBitVec (EvmYul.UInt256.land left right) =
      toBitVec left &&& toBitVec right := by
  rcases left with ⟨left⟩
  rcases right with ⟨right⟩
  have hAnd : left.val &&& right.val < 2^256 := by
    have h := (toBitVec ⟨left⟩ &&& toBitVec ⟨right⟩).isLt
    simpa [toBitVec, EvmYul.UInt256.toNat, BitVec.toNat_and,
      BitVec.toNat_ofNat, size_eq_two_pow,
      Nat.mod_eq_of_lt (by simpa [size_eq_two_pow] using left.isLt),
      Nat.mod_eq_of_lt (by simpa [size_eq_two_pow] using right.isLt)] using h
  have hAndSize : left.val &&& right.val < EvmYul.UInt256.size := by
    simpa [size_eq_two_pow] using hAnd
  apply BitVec.eq_of_toNat_eq
  simp [toBitVec, EvmYul.UInt256.toNat, EvmYul.UInt256.land, Fin.land,
    BitVec.toNat_and, BitVec.toNat_ofNat, size_eq_two_pow]
  exact Nat.mod_eq_of_lt hAndSize

theorem toBitVec_injective : Function.Injective toBitVec := by
  intro left right hEq
  rcases left with ⟨left⟩
  rcases right with ⟨right⟩
  congr 1
  apply Fin.ext
  have hNat := congrArg BitVec.toNat hEq
  simpa [toBitVec, EvmYul.UInt256.toNat, BitVec.toNat_ofNat,
    size_eq_two_pow,
    Nat.mod_eq_of_lt (by simpa [size_eq_two_pow] using left.isLt),
    Nat.mod_eq_of_lt (by simpa [size_eq_two_pow] using right.isLt)] using hNat

theorem lor_assoc (left middle right : EvmYul.UInt256) :
    EvmYul.UInt256.lor (EvmYul.UInt256.lor left middle) right =
      EvmYul.UInt256.lor left (EvmYul.UInt256.lor middle right) := by
  apply toBitVec_injective
  simp only [toBitVec_lor, BitVec.or_assoc]

theorem land_comm (left right : EvmYul.UInt256) :
    EvmYul.UInt256.land left right =
      EvmYul.UInt256.land right left := by
  apply toBitVec_injective
  simp only [toBitVec_land, BitVec.and_comm]

end UInt256

def mkOr (left right : Expr 1) : Expr 1 :=
  .prim .or (.cons left (.cons right .nil))

def mkAnd (left right : Expr 1) : Expr 1 :=
  .prim .and (.cons left (.cons right .nil))

def ExprSeq.ones? {results : Nat} :
    Locals.ExprSeq results → Option (List (Expr 1))
  | .nil => some []
  | @Locals.ExprSeq.cons left _right head tail => do
      if h : left = 1 then
        let head : Expr 1 := h ▸ head
        let rest ← ExprSeq.ones? tail
        some (head :: rest)
      else
        none

def Expr.orArgs? {results : Nat} : Expr results → Option (Expr 1 × Expr 1)
  | .prim op args => do
      if h : op = .or then
        have hInputs : Expressions.Structured.BasicOp.inputs op = 2 :=
          congrArg Expressions.Structured.BasicOp.inputs h
        let args : Locals.ExprSeq 2 := hInputs ▸ args
        match ← ExprSeq.ones? args with
        | [left, right] => some (left, right)
        | _ => none
      else
        none
  | _ => none

namespace ExprSeq

theorem ones?_eq_nil {results : Nat}
    (args : Locals.ExprSeq results)
    (h : ExprSeq.ones? args = some []) :
    Sigma.mk results args =
      Sigma.mk 0 (Locals.ExprSeq.nil : Locals.ExprSeq 0) := by
  cases args with
  | nil => rfl
  | @cons left right head tail =>
      simp [ExprSeq.ones?] at h
      rcases h with ⟨hLeft, h⟩
      cases hLeft
      rcases Option.bind_eq_some_iff.mp h with ⟨rest, hRest, hValues⟩
      simp at hValues

theorem ones?_eq_single {results : Nat}
    (args : Locals.ExprSeq results) {value : Expr 1}
    (h : ExprSeq.ones? args = some [value]) :
    Sigma.mk results args = Sigma.mk 1
      (@Locals.ExprSeq.cons 1 0 value Locals.ExprSeq.nil) := by
  cases args with
  | nil => simp [ExprSeq.ones?] at h
  | @cons left right head tail =>
      simp [ExprSeq.ones?] at h
      rcases h with ⟨hLeft, h⟩
      cases hLeft
      rcases Option.bind_eq_some_iff.mp h with ⟨rest, hRest, hValues⟩
      simp only [Option.some.injEq, List.cons.injEq] at hValues
      rcases hValues with ⟨rfl, rfl⟩
      have hTail := ones?_eq_nil tail hRest
      cases hTail
      rfl

theorem ones?_eq_pair {results : Nat}
    (args : Locals.ExprSeq results) {left right : Expr 1}
    (h : ExprSeq.ones? args = some [left, right]) :
    Sigma.mk results args = Sigma.mk 2
      (@Locals.ExprSeq.cons 1 1 left
        (@Locals.ExprSeq.cons 1 0 right Locals.ExprSeq.nil)) := by
  cases args with
  | nil => simp [ExprSeq.ones?] at h
  | @cons headResults tailResults head tail =>
      simp [ExprSeq.ones?] at h
      rcases h with ⟨hHead, h⟩
      cases hHead
      rcases Option.bind_eq_some_iff.mp h with ⟨rest, hRest, hValues⟩
      simp only [Option.some.injEq, List.cons.injEq] at hValues
      rcases hValues with ⟨rfl, rfl⟩
      have hTail := ones?_eq_single tail hRest
      cases hTail
      rfl

end ExprSeq

namespace Expr

theorem orArgs?_eq_mkOr {results : Nat} (expr : Expr results)
    {left right : Expr 1}
    (h : Expr.orArgs? expr = some (left, right)) :
    Sigma.mk results expr = Sigma.mk 1 (mkOr left right) := by
  cases expr with
  | lit => simp [Expr.orArgs?] at h
  | var => simp [Expr.orArgs?] at h
  | code code => simp [Expr.orArgs?] at h
  | prim op args =>
      simp [Expr.orArgs?] at h
      rcases h with ⟨hOp, h⟩
      cases hOp
      rcases Option.bind_eq_some_iff.mp h with ⟨values, hValues, hMatch⟩
      cases values with
      | nil => simp at hMatch
      | cons first rest =>
          cases rest with
          | nil => simp at hMatch
          | cons second tail =>
              cases tail with
              | cons third tail => simp at hMatch
              | nil =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at hMatch
                  rcases hMatch with ⟨rfl, rfl⟩
                  have hArgs := ExprSeq.ones?_eq_pair args hValues
                  cases hArgs
                  rfl

end Expr

def Expr.rotateOrFuel : Nat → Expr 1 → Expr 1
  | 0, expr => expr
  | fuel + 1, expr =>
      match Expr.orArgs? expr with
      | some (left, right) =>
          match Expr.orArgs? right with
          | some (middle, tail) =>
              Expr.rotateOrFuel fuel (mkOr (mkOr left middle) tail)
          | none => expr
      | none => expr

mutual
  def Expr.nodeCount {results : Nat} : Expr results → Nat
    | .lit _ | .var _ | .code _ => 1
    | .prim _ args => 1 + ExprSeq.nodeCount args

  def ExprSeq.nodeCount {results : Nat} : Locals.ExprSeq results → Nat
    | .nil => 0
    | .cons head tail => Expr.nodeCount head + ExprSeq.nodeCount tail
end

theorem Expr.nodeCount_pos {results : Nat} (expr : Expr results) :
    0 < Expr.nodeCount expr := by
  cases expr <;> simp [Expr.nodeCount]

def Expr.reassociateOr (expr : Expr 1) : Expr 1 :=
  Expr.rotateOrFuel (Expr.nodeCount expr) expr

def Expr.orderAnd (args : Locals.ExprSeq 2) : Expr 1 :=
  match ExprSeq.ones? args with
  | some [.lit value, right] => mkAnd right (.lit value)
  | _ => .prim .and args

def Expr.normalizePrim (op : Structured.BasicOp)
    (args : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op)) :
    Expr (Expressions.Structured.BasicOp.outputs op) :=
  match op with
  | .or => Expr.reassociateOr (.prim .or args)
  | .and => Expr.orderAnd args
  | op => .prim op args

mutual
  def Expr.normalize {results : Nat} : Expr results → Expr results
    | .lit value => .lit value
    | .var name => .var name
    | .code code => .code code
    | .prim op args => Expr.normalizePrim op (ExprSeq.normalize args)

  def ExprSeq.normalize {results : Nat} :
      Locals.ExprSeq results → Locals.ExprSeq results
    | .nil => .nil
    | .cons head tail =>
        .cons (Expr.normalize head) (ExprSeq.normalize tail)
end

mutual
  def Block.normalize : Block → Block
    | ⟨stmts⟩ => ⟨StmtList.normalize stmts⟩

  def Stmt.normalize : Stmt → Stmt
    | .expr expr => .expr (Expr.normalize expr)
    | .let_ name value => .let_ name (Expr.normalize value)
    | .assign name value => .assign name (Expr.normalize value)
    | .block body => .block (Block.normalize body)
    | .if_ cond body =>
        .if_ (Expr.normalize cond) (Block.normalize body)
    | .switch scrutinee cases defaultBody =>
        .switch (Expr.normalize scrutinee) (CaseList.normalize cases)
          (Default.normalize defaultBody)
    | .for_ init cond post body =>
        .for_ (Block.normalize init) (Expr.normalize cond)
          (Block.normalize post) (Block.normalize body)
    | .brk => .brk
    | .cont => .cont
    | .leave => .leave
    | .call targets functionName args =>
        .call targets functionName (args.map Expr.normalize)
    | .terminal kind => .terminal kind
    | .terminalArgs kind args =>
        .terminalArgs kind (ExprSeq.normalize args)

  def StmtList.normalize : List Stmt → List Stmt
    | [] => []
    | stmt :: rest => Stmt.normalize stmt :: StmtList.normalize rest

  def CaseList.normalize : List (Word × Block) → List (Word × Block)
    | [] => []
    | (value, body) :: rest =>
        (value, Block.normalize body) :: CaseList.normalize rest

  def Default.normalize : Option Block → Option Block
    | none => none
    | some body => some (Block.normalize body)
end

def FunDef.normalize (fn : FunDef) : FunDef :=
  { fn with body := Block.normalize fn.body }

def Program.normalize (program : Program) : Program :=
  { program with
    functions := program.functions.map FunDef.normalize
    body := Block.normalize program.body }

theorem FunList.find?_normalize (name : Name)
    (functions : List FunDef) :
    Functions.Source.FunList.find? name
        (functions.map FunDef.normalize) =
      (Functions.Source.FunList.find? name functions).map FunDef.normalize := by
  induction functions with
  | nil => rfl
  | cons fn rest ih =>
      by_cases hName : fn.name = name
      · simp [Functions.Source.FunList.find?, FunDef.normalize, hName]
      · simp [Functions.Source.FunList.find?, FunDef.normalize, hName, ih]

theorem Switch.select_normalize (value : Word)
    (cases : List (Word × Block)) (defaultBody : Option Block) :
    Functions.Source.Switch.select value (CaseList.normalize cases)
        (Default.normalize defaultBody) =
      (Functions.Source.Switch.select value cases defaultBody).map
        Block.normalize := by
  induction cases with
  | nil =>
      cases defaultBody <;> rfl
  | cons head rest ih =>
      rcases head with ⟨caseValue, body⟩
      by_cases hMatch : caseValue = value
      · simp [CaseList.normalize, Functions.Source.Switch.select, hMatch]
      · simp [CaseList.normalize, Functions.Source.Switch.select, hMatch, ih]

namespace ExprSeq

theorem openEval_single {results : Nat} (expr : Expr results)
    (state : Locals.InteractionSemantics.State) :
    Locals.InteractionSemantics.ExprSeq.openEval (.cons expr .nil) state =
      Locals.InteractionSemantics.Expr.openEval expr state := by
  unfold Locals.InteractionSemantics.ExprSeq.openEval
    Locals.InteractionSemantics.Expr.openEval
  simp only [Locals.Source.Effectful.Expr.Control.ExprSeq.eval]
  calc
    _ = Simulation.Interaction.bind
        (Locals.Source.Effectful.Expr.Control.eval
          Locals.InteractionSemantics.stateModel
          Locals.InteractionSemantics.primitiveSemantics expr state)
        Simulation.Interaction.pure := by
      apply Simulation.Interaction.AllDone.bind_congr
        (Simulation.Interaction.AllDone.trivial _)
      intro result _
      rcases result with ⟨after, values⟩
      change Simulation.Interaction.pure (after, values ++ []) =
        Simulation.Interaction.pure (after, values)
      rw [List.append_nil]
    _ = _ := Simulation.Interaction.bind_pure _

theorem openEval_two {leftResults rightResults : Nat}
    (left : Expr leftResults) (right : Expr rightResults)
    (state : Locals.InteractionSemantics.State) :
    Locals.InteractionSemantics.ExprSeq.openEval
        (.cons left (.cons right .nil)) state =
      Simulation.Interaction.bind
        (Locals.InteractionSemantics.Expr.openEval left state)
        (fun leftResult =>
          Simulation.Interaction.bind
            (Locals.InteractionSemantics.Expr.openEval right leftResult.1)
            (fun rightResult =>
              Simulation.Interaction.pure
                (rightResult.1, leftResult.2 ++ rightResult.2))) := by
  unfold Locals.InteractionSemantics.ExprSeq.openEval
    Locals.InteractionSemantics.Expr.openEval
  simp only [Locals.Source.Effectful.Expr.Control.ExprSeq.eval]
  change Simulation.Interaction.bind
      (Locals.InteractionSemantics.Expr.openEval left state)
      (fun leftResult =>
        Simulation.Interaction.bind
          (Locals.InteractionSemantics.ExprSeq.openEval
            (.cons right .nil) leftResult.1)
          (fun tailResult =>
            Simulation.Interaction.pure
              (tailResult.1, leftResult.2 ++ tailResult.2))) = _
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial _)
  intro leftResult _
  rw [openEval_single]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial _)
  intro rightResult _
  rfl

end ExprSeq

namespace Expr

theorem openEval_mkOr (left right : Expr 1)
    (state : Functions.InteractionSemantics.State) :
    Functions.InteractionSemantics.Expr.openEval (mkOr left right) state =
      Simulation.Interaction.bind
        (Functions.InteractionSemantics.Expr.openEvalOne left state)
        (fun leftResult =>
          Simulation.Interaction.bind
            (Functions.InteractionSemantics.Expr.openEvalOne
              right leftResult.1)
            (fun rightResult =>
              Simulation.Interaction.pure
                (rightResult.1,
                  [EvmYul.UInt256.lor rightResult.2 leftResult.2]))) := by
  unfold Functions.InteractionSemantics.Expr.openEval
    Functions.InteractionSemantics.Expr.openEvalOne
  unfold Locals.InteractionSemantics.Expr.openEval mkOr
  simp only [Locals.Source.Effectful.Expr.Control.eval]
  change Simulation.Interaction.bind
      (Locals.InteractionSemantics.ExprSeq.openEval
        (.cons left (.cons right .nil)) state)
      (fun args =>
        Locals.InteractionSemantics.Primitive.openEval
          .or args.1 args.2) = _
  rw [ExprSeq.openEval_two, Simulation.Interaction.bind_assoc]
  rw [Locals.InteractionSemantics.Expr.openEvalOne_eq_bind,
    Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Locals.InteractionArity.Expr.openEval_length left state)
  intro leftResult hLeft
  rcases leftResult with ⟨afterLeft, leftValues⟩
  change leftValues.length = 1 at hLeft
  cases leftValues with
  | nil => simp at hLeft
  | cons leftValue leftRest =>
      cases leftRest with
      | cons next tail => simp at hLeft
      | nil =>
          change
            Simulation.Interaction.bind
                (Simulation.Interaction.bind
                  (Locals.InteractionSemantics.Expr.openEval right afterLeft)
                  (fun result =>
                    Simulation.Interaction.pure
                      (result.1, [leftValue] ++ result.2)))
                (fun args =>
                  Locals.InteractionSemantics.Primitive.openEval
                    .or args.1 args.2) =
              Simulation.Interaction.bind
                (Locals.InteractionSemantics.Expr.openEvalOne right afterLeft)
                (fun rightResult =>
                  Simulation.Interaction.pure
                    (rightResult.1,
                      [EvmYul.UInt256.lor rightResult.2 leftValue]))
          rw [Simulation.Interaction.bind_assoc]
          rw [Locals.InteractionSemantics.Expr.openEvalOne_eq_bind,
            Simulation.Interaction.bind_assoc]
          apply Simulation.Interaction.AllDone.bind_congr
            (Locals.InteractionArity.Expr.openEval_length right afterLeft)
          intro rightResult hRight
          rcases rightResult with ⟨afterRight, rightValues⟩
          change rightValues.length = 1 at hRight
          cases rightValues with
          | nil => simp at hRight
          | cons rightValue rightRest =>
              cases rightRest with
              | cons next tail => simp at hRight
              | nil =>
                  change
                    Locals.InteractionSemantics.Primitive.openEval
                        .or afterRight [leftValue, rightValue] =
                      Simulation.Interaction.pure
                        (afterRight,
                          [EvmYul.UInt256.lor rightValue leftValue])
                  exact
                    Locals.InteractionSemantics.Primitive.openEval_or
                      afterRight leftValue rightValue

theorem openEval_mkAnd (left right : Expr 1)
    (state : Functions.InteractionSemantics.State) :
    Functions.InteractionSemantics.Expr.openEval (mkAnd left right) state =
      Simulation.Interaction.bind
        (Functions.InteractionSemantics.Expr.openEvalOne left state)
        (fun leftResult =>
          Simulation.Interaction.bind
            (Functions.InteractionSemantics.Expr.openEvalOne
              right leftResult.1)
            (fun rightResult =>
              Simulation.Interaction.pure
                (rightResult.1,
                  [EvmYul.UInt256.land rightResult.2 leftResult.2]))) := by
  unfold Functions.InteractionSemantics.Expr.openEval
    Functions.InteractionSemantics.Expr.openEvalOne
  unfold Locals.InteractionSemantics.Expr.openEval mkAnd
  simp only [Locals.Source.Effectful.Expr.Control.eval]
  change Simulation.Interaction.bind
      (Locals.InteractionSemantics.ExprSeq.openEval
        (.cons left (.cons right .nil)) state)
      (fun args =>
        Locals.InteractionSemantics.Primitive.openEval
          .and args.1 args.2) = _
  rw [ExprSeq.openEval_two, Simulation.Interaction.bind_assoc]
  rw [Locals.InteractionSemantics.Expr.openEvalOne_eq_bind,
    Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Locals.InteractionArity.Expr.openEval_length left state)
  intro leftResult hLeft
  rcases leftResult with ⟨afterLeft, leftValues⟩
  change leftValues.length = 1 at hLeft
  cases leftValues with
  | nil => simp at hLeft
  | cons leftValue leftRest =>
      cases leftRest with
      | cons next tail => simp at hLeft
      | nil =>
          change
            Simulation.Interaction.bind
                (Simulation.Interaction.bind
                  (Locals.InteractionSemantics.Expr.openEval right afterLeft)
                  (fun result =>
                    Simulation.Interaction.pure
                      (result.1, [leftValue] ++ result.2)))
                (fun args =>
                  Locals.InteractionSemantics.Primitive.openEval
                    .and args.1 args.2) =
              Simulation.Interaction.bind
                (Locals.InteractionSemantics.Expr.openEvalOne right afterLeft)
                (fun rightResult =>
                  Simulation.Interaction.pure
                    (rightResult.1,
                      [EvmYul.UInt256.land rightResult.2 leftValue]))
          rw [Simulation.Interaction.bind_assoc]
          rw [Locals.InteractionSemantics.Expr.openEvalOne_eq_bind,
            Simulation.Interaction.bind_assoc]
          apply Simulation.Interaction.AllDone.bind_congr
            (Locals.InteractionArity.Expr.openEval_length right afterLeft)
          intro rightResult hRight
          rcases rightResult with ⟨afterRight, rightValues⟩
          change rightValues.length = 1 at hRight
          cases rightValues with
          | nil => simp at hRight
          | cons rightValue rightRest =>
              cases rightRest with
              | cons next tail => simp at hRight
              | nil =>
                  change
                    Locals.InteractionSemantics.Primitive.openEval
                        .and afterRight [leftValue, rightValue] =
                      Simulation.Interaction.pure
                        (afterRight,
                          [EvmYul.UInt256.land rightValue leftValue])
                  exact
                    Locals.InteractionSemantics.Primitive.openEval_and
                      afterRight leftValue rightValue

theorem openEvalOne_mkOr (left right : Expr 1)
    (state : Functions.InteractionSemantics.State) :
    Functions.InteractionSemantics.Expr.openEvalOne (mkOr left right) state =
      Simulation.Interaction.bind
        (Functions.InteractionSemantics.Expr.openEvalOne left state)
        (fun leftResult =>
          Simulation.Interaction.bind
            (Functions.InteractionSemantics.Expr.openEvalOne
              right leftResult.1)
            (fun rightResult =>
              Simulation.Interaction.pure
                (rightResult.1,
                  EvmYul.UInt256.lor rightResult.2 leftResult.2))) := by
  unfold Functions.InteractionSemantics.Expr.openEvalOne
  rw [Locals.InteractionSemantics.Expr.openEvalOne_eq_bind]
  change Simulation.Interaction.bind
      (Functions.InteractionSemantics.Expr.openEval (mkOr left right) state)
      _ = _
  rw [openEval_mkOr, Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial _)
  intro leftResult _
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial _)
  intro rightResult _
  rfl

theorem openEvalOne_mkAnd (left right : Expr 1)
    (state : Functions.InteractionSemantics.State) :
    Functions.InteractionSemantics.Expr.openEvalOne (mkAnd left right) state =
      Simulation.Interaction.bind
        (Functions.InteractionSemantics.Expr.openEvalOne left state)
        (fun leftResult =>
          Simulation.Interaction.bind
            (Functions.InteractionSemantics.Expr.openEvalOne
              right leftResult.1)
            (fun rightResult =>
              Simulation.Interaction.pure
                (rightResult.1,
                  EvmYul.UInt256.land rightResult.2 leftResult.2))) := by
  unfold Functions.InteractionSemantics.Expr.openEvalOne
  rw [Locals.InteractionSemantics.Expr.openEvalOne_eq_bind]
  change Simulation.Interaction.bind
      (Functions.InteractionSemantics.Expr.openEval (mkAnd left right) state)
      _ = _
  rw [openEval_mkAnd, Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial _)
  intro leftResult _
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial _)
  intro rightResult _
  rfl

theorem openEvalOne_lit (value : EvmYul.UInt256)
    (state : Functions.InteractionSemantics.State) :
    Functions.InteractionSemantics.Expr.openEvalOne (.lit value) state =
      Simulation.Interaction.pure (state, value) := by
  rfl

theorem openEval_and_lit_comm (value : EvmYul.UInt256)
    (right : Expr 1) (state : Functions.InteractionSemantics.State) :
    Functions.InteractionSemantics.Expr.openEval
        (mkAnd (.lit value) right) state =
      Functions.InteractionSemantics.Expr.openEval
        (mkAnd right (.lit value)) state := by
  rw [openEval_mkAnd, openEval_mkAnd]
  simp_rw [openEvalOne_lit]
  change Simulation.Interaction.bind
      (Functions.InteractionSemantics.Expr.openEvalOne right state)
      (fun result =>
        Simulation.Interaction.pure
          (result.1, [EvmYul.UInt256.land result.2 value])) =
    Simulation.Interaction.bind
      (Functions.InteractionSemantics.Expr.openEvalOne right state)
      (fun result =>
        Simulation.Interaction.pure
          (result.1, [EvmYul.UInt256.land value result.2]))
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial _)
  intro result _
  rw [UInt256.land_comm]

theorem openEval_or_assoc (left middle right : Expr 1)
    (state : Functions.InteractionSemantics.State) :
    Functions.InteractionSemantics.Expr.openEval
        (mkOr left (mkOr middle right)) state =
      Functions.InteractionSemantics.Expr.openEval
        (mkOr (mkOr left middle) right) state := by
  rw [openEval_mkOr, openEval_mkOr]
  simp_rw [openEvalOne_mkOr]
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial _)
  intro leftResult _
  rw [Simulation.Interaction.bind_assoc,
    Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial _)
  intro middleResult _
  rw [Simulation.Interaction.bind_assoc]
  apply Simulation.Interaction.AllDone.bind_congr
    (Simulation.Interaction.AllDone.trivial _)
  intro rightResult _
  change Simulation.Interaction.pure
      (rightResult.1,
        [EvmYul.UInt256.lor
          (EvmYul.UInt256.lor rightResult.2 middleResult.2)
          leftResult.2]) = _
  rw [UInt256.lor_assoc]

theorem rotateOrFuel_openEval (fuel : Nat) (expr : Expr 1)
    (state : Functions.InteractionSemantics.State) :
    Functions.InteractionSemantics.Expr.openEval
        (Expr.rotateOrFuel fuel expr) state =
      Functions.InteractionSemantics.Expr.openEval expr state := by
  induction fuel generalizing expr state with
  | zero => rfl
  | succ fuel ih =>
      simp only [Expr.rotateOrFuel]
      split
      next left right hOuter =>
        split
        next middle tail hInner =>
          have hOuterEq := Expr.orArgs?_eq_mkOr expr hOuter
          cases hOuterEq
          have hInnerEq := Expr.orArgs?_eq_mkOr right hInner
          cases hInnerEq
          rw [ih]
          exact (openEval_or_assoc left middle tail state).symm
        next => rfl
      next => rfl

theorem orderAnd_openEval (args : Locals.ExprSeq 2)
    (state : Functions.InteractionSemantics.State) :
    Functions.InteractionSemantics.Expr.openEval (Expr.orderAnd args) state =
      Functions.InteractionSemantics.Expr.openEval (.prim .and args) state := by
  unfold Expr.orderAnd
  split
  next value right hArgs =>
    have hArgsEq := ExprSeq.ones?_eq_pair args hArgs
    cases hArgsEq
    exact (openEval_and_lit_comm value right state).symm
  next => rfl

theorem normalizePrim_openEval (op : Structured.BasicOp)
    (args : Locals.ExprSeq (Expressions.Structured.BasicOp.inputs op))
    (state : Functions.InteractionSemantics.State) :
    Functions.InteractionSemantics.Expr.openEval
        (Expr.normalizePrim op args) state =
      Functions.InteractionSemantics.Expr.openEval (.prim op args) state := by
  cases op <;> simp only [Expr.normalizePrim]
  · exact orderAnd_openEval args state
  · unfold Expr.reassociateOr
    exact Expr.rotateOrFuel_openEval _ _ state

end Expr

mutual
  theorem Expr.normalize_openEval {results : Nat}
      (expr : Expr results)
      (state : Functions.InteractionSemantics.State) :
      Functions.InteractionSemantics.Expr.openEval (Expr.normalize expr) state =
        Functions.InteractionSemantics.Expr.openEval expr state := by
    cases expr with
    | lit => rfl
    | var => rfl
    | code => rfl
    | prim op args =>
        simp only [Expr.normalize]
        rw [Expr.normalizePrim_openEval]
        unfold Functions.InteractionSemantics.Expr.openEval
          Locals.InteractionSemantics.Expr.openEval
        change Simulation.Interaction.bind
            (Locals.InteractionSemantics.ExprSeq.openEval
              (ExprSeq.normalize args) state) _ =
          Simulation.Interaction.bind
            (Locals.InteractionSemantics.ExprSeq.openEval args state) _
        rw [ExprSeq.normalize_openEval]
  termination_by 2 * Expr.nodeCount expr
  decreasing_by
    all_goals simp [Expr.nodeCount]
    all_goals omega

  theorem ExprSeq.normalize_openEval {results : Nat}
      (exprs : Locals.ExprSeq results)
      (state : Functions.InteractionSemantics.State) :
      Locals.InteractionSemantics.ExprSeq.openEval
          (ExprSeq.normalize exprs) state =
        Locals.InteractionSemantics.ExprSeq.openEval exprs state := by
    cases exprs with
    | nil => rfl
    | cons head tail =>
        simp only [ExprSeq.normalize]
        unfold Locals.InteractionSemantics.ExprSeq.openEval
          Locals.Source.Effectful.Expr.Control.ExprSeq.eval
        change Simulation.Interaction.bind
            (Functions.InteractionSemantics.Expr.openEval
              (Expr.normalize head) state)
            (fun headResult =>
              Simulation.Interaction.bind
                (Locals.InteractionSemantics.ExprSeq.openEval
                  (ExprSeq.normalize tail) headResult.1)
                (fun tailResult =>
                  Simulation.Interaction.pure
                    (tailResult.1, headResult.2 ++ tailResult.2))) = _
        rw [Expr.normalize_openEval]
        apply Simulation.Interaction.AllDone.bind_congr
          (Simulation.Interaction.AllDone.trivial _)
        intro result _
        rcases result with ⟨afterHead, headValues⟩
        change Simulation.Interaction.bind
            (Locals.InteractionSemantics.ExprSeq.openEval
              (ExprSeq.normalize tail) afterHead)
            (fun tailResult =>
              Simulation.Interaction.pure
                (tailResult.1, headValues ++ tailResult.2)) =
          Simulation.Interaction.bind
            (Locals.InteractionSemantics.ExprSeq.openEval tail afterHead)
            (fun tailResult =>
              Simulation.Interaction.pure
                (tailResult.1, headValues ++ tailResult.2))
        rw [ExprSeq.normalize_openEval]
  termination_by 2 * ExprSeq.nodeCount exprs + 1
  decreasing_by
    all_goals simp [ExprSeq.nodeCount]
    all_goals
      have hNodeCount := Expr.nodeCount_pos head
      omega
end

theorem Expr.normalize_openEvalOne (expr : Expr 1)
    (state : Functions.InteractionSemantics.State) :
    Functions.InteractionSemantics.Expr.openEvalOne
        (Expr.normalize expr) state =
      Functions.InteractionSemantics.Expr.openEvalOne expr state := by
  unfold Functions.InteractionSemantics.Expr.openEvalOne
  rw [Locals.InteractionSemantics.Expr.openEvalOne_eq_bind,
    Locals.InteractionSemantics.Expr.openEvalOne_eq_bind]
  change Simulation.Interaction.bind
      (Functions.InteractionSemantics.Expr.openEval
        (Expr.normalize expr) state) _ =
    Simulation.Interaction.bind
      (Functions.InteractionSemantics.Expr.openEval expr state) _
  rw [Expr.normalize_openEval]

theorem Expr.normalize_openEvalCondition (expr : Expr 1)
    (state : Functions.InteractionSemantics.State) :
    Functions.InteractionSemantics.Expr.openEvalCondition
        (Expr.normalize expr) state =
      Functions.InteractionSemantics.Expr.openEvalCondition expr state := by
  unfold Functions.InteractionSemantics.Expr.openEvalCondition
  rw [Locals.InteractionSemantics.Expr.openEvalCondition_eq_map_openEvalOne,
    Locals.InteractionSemantics.Expr.openEvalCondition_eq_map_openEvalOne]
  unfold Simulation.Interaction.map
  change Simulation.Interaction.bind
      (Functions.InteractionSemantics.Expr.openEvalOne
        (Expr.normalize expr) state) _ =
    Simulation.Interaction.bind
      (Functions.InteractionSemantics.Expr.openEvalOne expr state) _
  rw [Expr.normalize_openEvalOne]

theorem ArgList.normalize_openEval
    (args : List (Expr 1))
    (state : Functions.InteractionSemantics.State) :
    Functions.InteractionSemantics.ArgList.openEval
        (args.map Expr.normalize) state =
      Functions.InteractionSemantics.ArgList.openEval args state := by
  induction args generalizing state with
  | nil => rfl
  | cons head tail ih =>
      unfold Functions.InteractionSemantics.ArgList.openEval
        Functions.Source.Canonical.ArgList.eval
        Functions.Source.Effectful.ArgList.Control.eval
      simp only [List.map_cons]
      change Simulation.Interaction.bind
          (Functions.InteractionSemantics.Expr.openEvalOne
            (Expr.normalize head) state)
          (fun headResult =>
            Simulation.Interaction.bind
              (Functions.InteractionSemantics.ArgList.openEval
                (tail.map Expr.normalize) headResult.1)
              (fun tailResult =>
                Simulation.Interaction.pure
                  (tailResult.1, headResult.2 :: tailResult.2))) = _
      rw [Expr.normalize_openEvalOne]
      apply Simulation.Interaction.AllDone.bind_congr
        (Simulation.Interaction.AllDone.trivial _)
      intro result _
      rcases result with ⟨afterHead, value⟩
      change Simulation.Interaction.bind
          (Functions.InteractionSemantics.ArgList.openEval
            (tail.map Expr.normalize) afterHead)
          (fun tailResult =>
            Simulation.Interaction.pure
              (tailResult.1, value :: tailResult.2)) =
        Simulation.Interaction.bind
          (Functions.InteractionSemantics.ArgList.openEval tail afterHead)
          (fun tailResult =>
            Simulation.Interaction.pure
              (tailResult.1, value :: tailResult.2))
      rw [ih]

end StackPressureNormalization
end Functions
end EvmCompiler
