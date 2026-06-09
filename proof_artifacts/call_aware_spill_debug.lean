import EvmCompiler.Functions.CallAwareSpill

open EvmCompiler
open EvmCompiler.Functions
open EvmCompiler.Functions.CallAwareSpill

def dbgRange : ScratchRange := plannedScratchRange 64

def lit0 : Expr 1 := .lit (EvmYul.UInt256.ofNat 0)
def lit6 : Expr 1 := .lit (EvmYul.UInt256.ofNat 6)
def divX6 : Expr 1 :=
  .prim .div (.cons (.var "x") (.cons lit6 .nil))

def dbgFn : FunDef :=
  { name := "wrapping_div_uint256"
    params := ["x"]
    returns := ["r"]
    body :=
      { stmts :=
          [ .let_ "_1" lit0
          , .assign "_1" lit0
          , .assign "r" divX6 ] } }

def dbgProgram : Program :=
  { functions := [dbgFn]
    body := { stmts := [] } }

#eval (compileFunDefWithSwitchFallback? dbgRange dbgProgram dbgFn).isSome

#eval
  match
      compileLocalsBlockSpan? dbgRange dbgFn.params dbgFn.params.reverse
        (layoutOfParamStack dbgFn.params)
        { stmts := initReturnsInSourceScopeOrder dbgFn.returns } with
  | none => "init none"
  | some init =>
      match
          compileBlockOpenWithSwitchFallback? dbgRange dbgProgram dbgFn.returns
            init.sourceScope init.stackLayout init.layout dbgFn.body with
      | none => "body none"
      | some body =>
          match
              appendReturnFallthrough? dbgRange dbgFn.returns
                { sourceScope := body.sourceScope
                  stackLayout := body.stackLayout
                  layout := body.layout
                  block := ExpressionsBlock.append init.block body.block } with
          | none => "return none"
          | some _ => "return some"
