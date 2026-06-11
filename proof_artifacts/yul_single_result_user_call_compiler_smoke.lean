import EvmCompiler.Yul.Compiler
import EvmCompiler.Solidity.BridgeJson

/-!
Smoke checks for single-result call lowering.

These checks pin the imported-Yul compiler surface where a user function with
one result can be used directly as an expression, including nested under a
primitive expression and in control-condition positions. They also pin
multi-result declaration/assignment calls, which are Yul statement forms rather
than expressions. The final guards pin single-result external/account
primitives that share the same expression frontier, plus the object-builtin
frontend path that resolves object/data pseudo-builtins before core lowering.
-/

namespace EvmCompiler
namespace Yul

noncomputable section

def smokeSome {α : Type} : Option α → Bool
  | some _ => true
  | none => false

def smokeOne : Word :=
  EvmYul.UInt256.ofNat 1

def smokeFrontendUserCallExpr : Solidity.Frontend.Expr :=
  .call .user "f" [.var "a", .lit smokeOne]

def smokeFrontendSingleCallProgram : Solidity.Frontend.Program :=
  { source := "Smoke.sol"
    contract := "Smoke"
    object :=
      { name := "runtime"
        dispatcher := [.letDecl ["x"] (some (.call .user "f" []))]
        functions :=
          [("f",
            { params := []
              returns := ["r"]
              body := [.assign ["r"] (.lit smokeOne)] })]
        data := []
        objects := []
        items := [] } }

def smokeFrontendNestedFunctionStmtProgram : Solidity.Frontend.Program :=
  { source := "NestedFunctionSmoke.sol"
    contract := "NestedFunctionSmoke"
    object :=
      { name := "runtime"
        dispatcher :=
          [ .functionDef "f" [] ["r"] [.assign ["r"] (.lit smokeOne)]
          , .letDecl ["x"] (some (.call .user "__yul_gen_0_f" [])) ]
        functions :=
          [("__yul_gen_0_f",
            { params := []
              returns := ["r"]
              body := [.assign ["r"] (.lit smokeOne)] })]
        data := []
        objects := []
        items := [] } }

def smokeFrontendControlCallProgram : Solidity.Frontend.Program :=
  { source := "ControlSmoke.sol"
    contract := "ControlSmoke"
    object :=
      { name := "runtime"
        dispatcher :=
          [ .ifThen (.call .user "f" []) []
          , .switch (.call .user "f" []) [(.word smokeOne, [])] []
          , .forLoop [] (.call .user "f" []) [] [] ]
        functions :=
          [("f",
            { params := []
              returns := ["r"]
              body := [.assign ["r"] (.lit smokeOne)] })]
        data := []
        objects := []
        items := [] } }

def smokeBridgeJsonSingleCall : String :=
  "{\"schema\":\"evm-compiler.solc-yul-bridge.v3\",\"source\":\"Smoke.sol\",\"contract\":\"Smoke\",\"selectedObject\":{\"node\":\"object\",\"name\":\"runtime\",\"dispatcher\":[{\"node\":\"let\",\"names\":[\"x\"],\"value\":{\"node\":\"call\",\"calleeKind\":\"user\",\"callee\":\"f\",\"args\":[]}}],\"functions\":[{\"name\":\"f\",\"params\":[],\"returns\":[\"r\"],\"body\":[{\"node\":\"assign\",\"names\":[\"r\"],\"value\":{\"node\":\"literal\",\"value\":1}}]}],\"data\":[],\"subobjects\":[],\"items\":[]}}"

def smokeBridgeJsonNestedFunctionStmt : String :=
  "{\"schema\":\"evm-compiler.solc-yul-bridge.v3\",\"source\":\"NestedFunctionSmoke.sol\",\"contract\":\"NestedFunctionSmoke\",\"selectedObject\":{\"node\":\"object\",\"name\":\"runtime\",\"dispatcher\":[{\"node\":\"function\",\"name\":\"f\",\"params\":[],\"returns\":[\"r\"],\"body\":[{\"node\":\"assign\",\"names\":[\"r\"],\"value\":{\"node\":\"literal\",\"value\":1}}]},{\"node\":\"let\",\"names\":[\"x\"],\"value\":{\"node\":\"call\",\"calleeKind\":\"user\",\"callee\":\"__yul_gen_0_f\",\"args\":[]}}],\"functions\":[{\"name\":\"__yul_gen_0_f\",\"params\":[],\"returns\":[\"r\"],\"body\":[{\"node\":\"assign\",\"names\":[\"r\"],\"value\":{\"node\":\"literal\",\"value\":1}}]}],\"data\":[],\"subobjects\":[],\"items\":[]}}"

def smokeBridgeJsonSwitchCaseLiterals : String :=
  "{\"schema\":\"evm-compiler.solc-yul-bridge.v3\",\"source\":\"SwitchSmoke.sol\",\"contract\":\"SwitchSmoke\",\"selectedObject\":{\"node\":\"object\",\"name\":\"runtime\",\"dispatcher\":[{\"node\":\"switch\",\"scrutinee\":{\"node\":\"var\",\"name\":\"x\"},\"cases\":[{\"value\":{\"node\":\"stringLiteral\",\"value\":\"ok\"},\"body\":[]},{\"value\":{\"node\":\"bytesLiteral\",\"bytes\":[255]},\"body\":[]},{\"value\":{\"node\":\"boolLiteral\",\"value\":true},\"body\":[]}],\"default\":[]}],\"functions\":[],\"data\":[],\"subobjects\":[],\"items\":[]}}"

def smokeFrontendForWithInit : Solidity.Frontend.Stmt :=
  .forLoop
    [.letDecl ["i"] (some (.lit smokeOne))]
    (.call .primitive "lt" [.var "i", .lit smokeOne])
    [.assign ["i"] (.call .primitive "add" [.var "i", .lit smokeOne])]
    []

def smokeUserCall : AstExpr :=
  .Call (.inr "f") []

def smokeUserCallWithDirectArgs : AstExpr :=
  .Call (.inr "f") [.Var "a", .Lit smokeOne]

def smokeNestedUserCall : AstExpr :=
  .Call (.inl ((.StopArith .ADD : EvmYul.Operation .Yul)))
    [smokeUserCall, .Lit smokeOne]

def smokeNestedUserCallArg : AstExpr :=
  .Call (.inr "f") [.Call (.inr "g") []]

def smokeTwoUserCallsInPrimitive : AstExpr :=
  .Call (.inl ((.StopArith .ADD : EvmYul.Operation .Yul)))
    [.Call (.inr "f") [], .Call (.inr "g") []]

def smokeDirectLetUserCall : AstStmt :=
  .Let ["x"] (some smokeUserCall)

def smokeDirectAssignUserCall : AstStmt :=
  .Assign ["x"] smokeUserCall

def smokeDirectLetUserCallWithArgs : AstStmt :=
  .Let ["x"] (some smokeUserCallWithDirectArgs)

def smokeDirectAssignUserCallWithArgs : AstStmt :=
  .Assign ["x"] smokeUserCallWithDirectArgs

def smokeLetNestedUserCallArg : AstStmt :=
  .Let ["x"] (some smokeNestedUserCallArg)

def smokeAssignNestedUserCallArg : AstStmt :=
  .Assign ["x"] smokeNestedUserCallArg

def smokeMultiLetUserCall : AstStmt :=
  .Let ["x", "y"] (some smokeUserCall)

def smokeMultiAssignUserCall : AstStmt :=
  .Assign ["x", "y"] smokeUserCall

def smokeNestedLetUserCall : AstStmt :=
  .Let ["x"] (some smokeNestedUserCall)

def smokeIfUserCall : AstStmt :=
  .If smokeUserCall []

def smokeSwitchUserCall : AstStmt :=
  .Switch smokeUserCall [] []

def smokeForUserCall : AstStmt :=
  .For smokeUserCall [] []

def smokeExprStmtUserCall : AstStmt :=
  .ExprStmtCall smokeUserCall

def smokeStopStmt : AstStmt :=
  .ExprStmtCall
    (.Call (.inl ((.StopArith .STOP : EvmYul.Operation .Yul))) [])

def smokeReturnStmt : AstStmt :=
  .ExprStmtCall
    (.Call (.inl ((.System .RETURN : EvmYul.Operation .Yul)))
      [.Lit smokeOne, .Lit smokeOne])

def smokeRevertStmt : AstStmt :=
  .ExprStmtCall
    (.Call (.inl ((.System .REVERT : EvmYul.Operation .Yul)))
      [.Lit smokeOne, .Lit smokeOne])

def smokeSelfdestructStmt : AstStmt :=
  .ExprStmtCall
    (.Call (.inl ((.System .SELFDESTRUCT : EvmYul.Operation .Yul)))
      [.Lit smokeOne])

def smokeExternalCallExpr : AstExpr :=
  .Call (.inl ((.System .CALL : EvmYul.Operation .Yul)))
    [.Lit smokeOne, .Lit smokeOne, .Lit smokeOne, .Lit smokeOne,
      .Lit smokeOne, .Lit smokeOne, .Lit smokeOne]

def smokeExternalCallcodeExpr : AstExpr :=
  .Call (.inl ((.System .CALLCODE : EvmYul.Operation .Yul)))
    [.Lit smokeOne, .Lit smokeOne, .Lit smokeOne, .Lit smokeOne,
      .Lit smokeOne, .Lit smokeOne, .Lit smokeOne]

def smokeExternalStaticCallExpr : AstExpr :=
  .Call (.inl ((.System .STATICCALL : EvmYul.Operation .Yul)))
    [.Lit smokeOne, .Lit smokeOne, .Lit smokeOne, .Lit smokeOne,
      .Lit smokeOne, .Lit smokeOne]

def smokeExternalDelegateCallExpr : AstExpr :=
  .Call (.inl ((.System .DELEGATECALL : EvmYul.Operation .Yul)))
    [.Lit smokeOne, .Lit smokeOne, .Lit smokeOne, .Lit smokeOne,
      .Lit smokeOne, .Lit smokeOne]

def smokeGasExpr : AstExpr :=
  .Call (.inl ((.StackMemFlow .GAS : EvmYul.Operation .Yul))) []

def smokeWideUncheckedAbiCallExpr : AstExpr :=
  .Call (.inl ((.System .CALL : EvmYul.Operation .Yul)))
    [ smokeGasExpr
    , .Call (.inl ((.CompBit .AND : EvmYul.Operation .Yul)))
        [ .Var "value1_1"
        , .Lit (EvmYul.UInt256.ofNat
            1461501637330902918203684832716283019655932542975) ]
    , .Lit (EvmYul.UInt256.ofNat 0)
    , .Var "_14"
    , .Call (.inl ((.StopArith .SUB : EvmYul.Operation .Yul)))
        [ .Call (.inr "abi_encode_string")
            [ .Var "array"
            , .Call (.inl ((.StopArith .ADD : EvmYul.Operation .Yul)))
                [ .Var "_14", .Lit (EvmYul.UInt256.ofNat 132) ] ]
        , .Var "_14" ]
    , .Var "_14"
    , .Lit (EvmYul.UInt256.ofNat 32) ]

def smokeWideUncheckedCallStmt : AstStmt :=
  .Block
    [ .Let ["value1_1"] (some (.Lit smokeOne))
    , .Let ["value0_3"] (some (.Lit smokeOne))
    , .Let ["offset_2"] (some (.Lit smokeOne))
    , .Let ["value_6"] (some (.Lit smokeOne))
    , .Let ["dummy_0"] (some (.Lit smokeOne))
    , .Let ["dummy_1"] (some (.Lit smokeOne))
    , .Let ["dummy_2"] (some (.Lit smokeOne))
    , .Let ["dummy_3"] (some (.Lit smokeOne))
    , .Let ["array"] (some (.Lit smokeOne))
    , .Let ["_14"] (some (.Lit smokeOne))
    , .Let ["_15"] (some smokeWideUncheckedAbiCallExpr) ]

def smokeWideUncheckedAbiEncodeStringFn : Functions.FunDef :=
  { name := "abi_encode_string"
    params := ["array", "ptr"]
    returns := ["r"]
    body := { stmts := [.assign "r" (.var "ptr")] } }

def smokeWideUncheckedFreshNames : List Name :=
  [ "value1_1", "value0_3", "offset_2", "value_6", "dummy_0"
  , "dummy_1", "dummy_2", "dummy_3", "array", "_14", "_15"
  , "abi_encode_string" ]

def smokeWideUncheckedFunctionsProgram? : Option Functions.Program := do
  let initial := Fresh.initial smokeWideUncheckedFreshNames
  let (bodyStmts, _state) ←
    Stmt.toFunctionsListUncheckedFuel? 128 initial smokeWideUncheckedCallStmt
  some
    { functions := [smokeWideUncheckedAbiEncodeStringFn]
      body := { stmts := bodyStmts } }

def smokeDeepPureAliasExpr : Nat → AstExpr
  | 0 => .Var "deep"
  | depth + 1 =>
      .Call (.inl ((.StopArith .ADD : EvmYul.Operation .Yul)))
        [smokeDeepPureAliasExpr depth, .Var "deep"]

def smokeDeepPureAliasMaterializes : Bool :=
  match
      Expr.lower1Unchecked?
        (Fresh.initial ["deep"])
        (smokeDeepPureAliasExpr 16) with
  | some (pre, _expr, _state) => !pre.isEmpty
  | none => false

def smokeShallowPureAliasStaysDirect : Bool :=
  match
      Expr.lower1Unchecked?
        (Fresh.initial ["deep"])
        (smokeDeepPureAliasExpr 4) with
  | some (pre, _expr, _state) => pre.isEmpty
  | none => false

def smokeCreateExpr : AstExpr :=
  .Call (.inl ((.System .CREATE : EvmYul.Operation .Yul)))
    [.Lit smokeOne, .Lit smokeOne, .Lit smokeOne]

def smokeCreate2Expr : AstExpr :=
  .Call (.inl ((.System .CREATE2 : EvmYul.Operation .Yul)))
    [.Lit smokeOne, .Lit smokeOne, .Lit smokeOne, .Lit smokeOne]

def smokeBalanceExpr : AstExpr :=
  .Call (.inl ((.Env .BALANCE : EvmYul.Operation .Yul))) [.Lit smokeOne]

def smokeExtcodesizeExpr : AstExpr :=
  .Call (.inl ((.Env .EXTCODESIZE : EvmYul.Operation .Yul))) [.Lit smokeOne]

def smokeExtcodehashExpr : AstExpr :=
  .Call (.inl ((.Env .EXTCODEHASH : EvmYul.Operation .Yul))) [.Lit smokeOne]

def smokeExtcodecopyStmt : AstStmt :=
  .ExprStmtCall
    (.Call (.inl ((.Env .EXTCODECOPY : EvmYul.Operation .Yul)))
      [.Lit smokeOne, .Lit smokeOne, .Lit smokeOne, .Lit smokeOne])

def smokeObjectDataBytes : List UInt8 :=
  [1, 2, 3]

def smokeObjectNameBytes : List UInt8 :=
  [98, 108, 111, 98]

def smokeLinkerSymbolNameBytes : List UInt8 :=
  [76, 73, 66]

def smokeImmutableNameBytes : List UInt8 :=
  [73, 77, 77]

def smokeObjectLayout : Solidity.Frontend.ObjectLayout :=
  { entries := [] }

def smokeObjectProgram : Solidity.Frontend.Program :=
  { source := "ObjectSmoke.sol"
    contract := "ObjectSmoke"
    object :=
      { name := "runtime"
        dispatcher :=
          [ .letDecl ["size"]
              (some
                (.call .objectBuiltin "datasize" [.stringLit "blob"]))
          , .letDecl ["offset"]
              (some
                (.call .objectBuiltin "dataoffset" [.stringLit "blob"]))
          , .letDecl ["guard"]
              (some
                (.call .objectBuiltin "memoryguard"
                  [.lit (EvmYul.UInt256.ofNat 128)]))
          , .exprStmt
              (.call .objectBuiltin "datacopy"
                [ .lit (EvmYul.UInt256.ofNat 0)
                , .call .objectBuiltin "dataoffset" [.stringLit "blob"]
                , .call .objectBuiltin "datasize" [.stringLit "blob"] ]) ]
        functions := []
        data := [{ name? := some "blob", bytes := smokeObjectDataBytes }]
        objects := []
        items := [.data 0] } }

def smokeDataSizeOnlyObject : Solidity.Frontend.Object :=
  { name := "runtime"
    dispatcher :=
      [ .letDecl ["size"]
          (some (.call .objectBuiltin "datasize" [.stringLit "blob"]))
      , .exprStmt (.call .primitive "stop" []) ]
    functions := []
    data := [{ name? := some "blob", bytes := smokeObjectDataBytes }]
    objects := []
    items := [.data 0] }

def smokeImmutableOnlyObject : Solidity.Frontend.Object :=
  { name := "runtime"
    dispatcher :=
      [ .exprStmt
          (.call .primitive "mstore"
            [ .lit (EvmYul.UInt256.ofNat 0)
            , .call .objectBuiltin "loadimmutable"
                [.stringLit "IMM"] ])
      , .exprStmt (.call .primitive "stop" []) ]
    functions := []
    data := []
    objects := []
    items := [] }

def smokeMarkerCollisionObject : Solidity.Frontend.Object :=
  { smokeImmutableOnlyObject with
    dispatcher :=
      [ .exprStmt
          (.call .primitive "mstore"
            [ .lit (EvmYul.UInt256.ofNat 0)
            , .lit
                (Solidity.Frontend.ImmutableReference.markerValue 0) ])
      , .exprStmt
          (.call .primitive "mstore"
            [ .lit (EvmYul.UInt256.ofNat 32)
            , .call .objectBuiltin "loadimmutable"
                [.stringLit "IMM"] ])
      , .exprStmt (.call .primitive "stop" []) ] }

def smokeObjectContext : Solidity.Frontend.ObjectBuiltinContext :=
  { layout := smokeObjectLayout
    dataSizes := [("blob", EvmYul.UInt256.ofNat smokeObjectDataBytes.length)]
    dataOffsets := [("blob", EvmYul.UInt256.ofNat 64)]
    linkerSymbols := [("LIB", smokeOne)] }

def smokeImmutableContext : Solidity.Frontend.ObjectBuiltinContext :=
  { smokeObjectContext with
    immutableValues := [("IMM", smokeOne)] }

def smokeSetImmutableContext : Solidity.Frontend.ObjectBuiltinContext :=
  { smokeObjectContext with
    immutableReferences := [("IMM", [{ start := 7, length := 32 }])] }

def smokeSetImmutableNoReferenceContext :
    Solidity.Frontend.ObjectBuiltinContext :=
  smokeObjectContext

#guard ObjectBuiltin.unsupported? "f" = false
#guard ObjectBuiltin.unsupported? "datasize" = true
#guard ObjectBuiltin.unsupported? "dataoffset" = true
#guard ObjectBuiltin.unsupported? "datacopy" = true
#guard ObjectBuiltin.unsupported? "setimmutable" = true
#guard ObjectBuiltin.unsupported? "loadimmutable" = true
#guard ObjectBuiltin.unsupported? "linkersymbol" = true
#guard ObjectBuiltin.unsupported? "memoryguard" = true

#guard smokeObjectProgram.object.codeUsesCodeLayoutBuiltin? = true

#guard smokeDataSizeOnlyObject.codeUsesCodeLayoutBuiltin? = false

#guard smokeImmutableOnlyObject.codeUsesCodeLayoutBuiltin? = false

#guard
  smokeImmutableOnlyObject.canUseSingleImmutableMarkerPass?
    (Solidity.Frontend.ImmutableReference.markerEntriesFromNat 0 ["IMM"]) =
      true

#guard
  smokeMarkerCollisionObject.canUseSingleImmutableMarkerPass?
    (Solidity.Frontend.ImmutableReference.markerEntriesFromNat 0 ["IMM"]) =
      false

#guard
  (match
      smokeDataSizeOnlyObject.computedImageUncheckedWithLinkerSymbols? [] with
  | some (computed, image) =>
      computed.codeBase == computed.code.length &&
        computed.markerCode == computed.code &&
          image.bytes.length == computed.codeBase + computed.payload.length
  | none => false) = true

#guard
  (match
      smokeImmutableOnlyObject.computedImageUncheckedWithLinkerSymbols? [] with
  | some (computed, image) =>
      computed.codeBase == computed.code.length &&
        computed.markerCode.length == computed.codeBase &&
          !(computed.markerCode == computed.code) &&
            image.bytes.length == computed.codeBase &&
              match image.immutableReferences with
            | [("IMM", refs)] => !refs.isEmpty
            | _ => false
  | none => false) = true

#guard
  Prim.terminal? ((.StopArith .STOP : EvmYul.Operation .Yul)) =
    some .stop

#guard
  Prim.terminal? ((.System .RETURN : EvmYul.Operation .Yul)) =
    some .return

#guard
  Prim.terminal? ((.System .REVERT : EvmYul.Operation .Yul)) =
    some .revert

#guard
  Prim.terminal? ((.System .SELFDESTRUCT : EvmYul.Operation .Yul)) =
    some .selfdestruct

#guard
  (match Solidity.Frontend.Expr.toYul? smokeFrontendUserCallExpr with
  | some (.Call (.inr "f") [.Var "a", .Lit value]) =>
      value.toNat == smokeOne.toNat
  | _ => false) = true

#guard
  (match smokeFrontendSingleCallProgram.toYulProgram? with
  | some program =>
      match program.contract.dispatcher with
      | .Block [.Let ["x"] (some (.Call (.inr "f") []))] => true
      | _ => false
  | none => false) = true

#guard
  (match smokeFrontendNestedFunctionStmtProgram.toYulProgram? with
  | some program =>
      match program.contract.dispatcher with
      | .Block
          [ .Block []
          , .Let ["x"] (some (.Call (.inr "__yul_gen_0_f") [])) ] => true
      | _ => false
  | none => false) = true

#guard
  (match smokeFrontendControlCallProgram.toYulProgram? with
  | some program =>
      match program.contract.dispatcher with
      | .Block
          [ .If (.Call (.inr "f") []) []
          , .Switch (.Call (.inr "f") []) [(value, [])] []
          , .For (.Call (.inr "f") []) [] [] ] =>
            value.toNat == smokeOne.toNat
      | _ => false
  | none => false) = true

#guard
  (match Solidity.Frontend.Stmt.toYul? smokeFrontendForWithInit with
  | some (.Block [.Let ["i"] (some (.Lit value)), .For _ _ _]) =>
      value.toNat == smokeOne.toNat
  | _ => false) = true

#guard
  (match Solidity.Frontend.BridgeJson.parseProgram? smokeBridgeJsonSingleCall with
  | .ok program =>
      match program.toYulProgram? with
      | some yul =>
          match yul.contract.dispatcher with
          | .Block [.Let ["x"] (some (.Call (.inr "f") []))] => true
          | _ => false
      | none => false
  | .error _ => false) = true

#guard
  (match Solidity.Frontend.BridgeJson.parseProgram?
      smokeBridgeJsonNestedFunctionStmt with
  | .ok program =>
      match program.toYulProgram? with
      | some yul =>
          match yul.contract.dispatcher with
          | .Block
              [ .Block []
              , .Let ["x"] (some (.Call (.inr "__yul_gen_0_f") [])) ] => true
          | _ => false
      | none => false
  | .error _ => false) = true

#guard
  (match Solidity.Frontend.BridgeJson.parseProgram?
      smokeBridgeJsonSwitchCaseLiterals with
  | .ok program =>
      match program.toYulProgram? with
      | some yul =>
          match yul.contract.dispatcher with
          | .Block
              [ .Switch (.Var "x")
                  [(okValue, []), (ffValue, []), (boolValue, [])] [] ] =>
              match
                Solidity.Frontend.StringLiteral.word? "ok",
                Solidity.Frontend.StringLiteral.wordBytes?
                  [(UInt8.ofNat 255)]
              with
              | some expectedOk, some expectedFf =>
                  okValue.toNat == expectedOk.toNat &&
                    ffValue.toNat == expectedFf.toNat &&
                    boolValue.toNat == 1
              | _, _ => false
          | _ => false
      | none => false
  | .error _ => false) = true

#guard
  smokeSome
    (Expr.lower1? (Fresh.initial (Expr.names smokeUserCall))
      smokeUserCall) = true

#guard
  Expr.directCallArgSafe? (.Var "a") = true

#guard
  Expr.directCallArgSafe? (.Lit smokeOne) = true

#guard
  Expr.List.directCallArgsSafe? [] = true

#guard
  Expr.List.directCallArgsSafe? [.Var "a", .Lit smokeOne] = false

#guard
  Expr.List.directCallArgsSafe? [.Call (.inr "g") []] = false

#guard
  smokeSome
    (Expr.lower1? (Fresh.initial (Expr.names smokeUserCallWithDirectArgs))
      smokeUserCallWithDirectArgs) = true

#guard
  smokeSome
    (Expr.lower1? (Fresh.initial (Expr.names smokeNestedUserCall))
      smokeNestedUserCall) = true

#guard
  smokeSome
    (Expr.lower1? (Fresh.initial (Expr.names smokeNestedUserCallArg))
      smokeNestedUserCallArg) = true

#guard
  smokeSome
    (Expr.lower1? (Fresh.initial (Expr.names smokeTwoUserCallsInPrimitive))
      smokeTwoUserCallsInPrimitive) = true

#guard
  smokeSome
    (Stmt.toFunctionsListFuel? 16
      (Fresh.initial (Stmt.names smokeDirectLetUserCall))
      smokeDirectLetUserCall) = true

#guard
  smokeSome
    (Stmt.toFunctionsListFuel? 16
      (Fresh.initial (Stmt.names smokeDirectAssignUserCall))
      smokeDirectAssignUserCall) = true

#guard
  smokeSome
    (Stmt.toFunctionsListFuel? 16
      (Fresh.initial (Stmt.names smokeDirectLetUserCallWithArgs))
      smokeDirectLetUserCallWithArgs) = true

#guard
  smokeSome
    (Stmt.toFunctionsListFuel? 16
      (Fresh.initial (Stmt.names smokeDirectAssignUserCallWithArgs))
      smokeDirectAssignUserCallWithArgs) = true

#guard
  smokeSome
    (Stmt.toFunctionsListFuel? 16
      (Fresh.initial (Stmt.names smokeLetNestedUserCallArg))
      smokeLetNestedUserCallArg) = true

#guard
  smokeSome
    (Stmt.toFunctionsListFuel? 16
      (Fresh.initial (Stmt.names smokeAssignNestedUserCallArg))
      smokeAssignNestedUserCallArg) = true

#guard
  smokeSome
    (Stmt.toFunctionsListFuel? 16
      (Fresh.initial (Stmt.names smokeNestedLetUserCall))
      smokeNestedLetUserCall) = true

#guard
  (match
      Stmt.toFunctionsListFuel? 16
        (Fresh.initial (Stmt.names smokeDirectLetUserCall))
        smokeDirectLetUserCall with
    | some
        ([Functions.Stmt.let_ "x" _,
          Functions.Stmt.call ["x"] "f" []], _) => true
    | _ => false) = true

#guard
  (match
      Stmt.toFunctionsListFuel? 16
        (Fresh.initial (Stmt.names smokeDirectAssignUserCall))
        smokeDirectAssignUserCall with
    | some ([Functions.Stmt.call ["x"] "f" []], _) => true
    | _ => false) = true

#guard
  (match
      Stmt.toFunctionsListFuel? 16
        (Fresh.initial (Stmt.names smokeMultiLetUserCall))
        smokeMultiLetUserCall with
    | some
        ([Functions.Stmt.let_ "x" _,
          Functions.Stmt.let_ "y" _,
          Functions.Stmt.call ["x", "y"] "f" []], _) => true
    | _ => false) = true

#guard
  (match
      Stmt.toFunctionsListFuel? 16
        (Fresh.initial (Stmt.names smokeMultiAssignUserCall))
        smokeMultiAssignUserCall with
    | some ([Functions.Stmt.call ["x", "y"] "f" []], _) => true
    | _ => false) = true

#guard
  smokeSome
    (Stmt.toFunctionsListFuel? 16
      (Fresh.initial (Stmt.names smokeIfUserCall))
      smokeIfUserCall) = true

#guard
  smokeSome
    (Stmt.toFunctionsListFuel? 16
      (Fresh.initial (Stmt.names smokeSwitchUserCall))
      smokeSwitchUserCall) = true

#guard
  smokeSome
    (Stmt.toFunctionsListFuel? 16
      (Fresh.initial (Stmt.names smokeForUserCall))
      smokeForUserCall) = true

#guard
  smokeSome
    (Stmt.toFunctionsListFuel? 16
      (Fresh.initial (Stmt.names smokeExprStmtUserCall))
      smokeExprStmtUserCall) = true

#guard
  smokeSome
    (Stmt.toFunctionsListFuel? 16
      (Fresh.initial (Stmt.names smokeStopStmt))
      smokeStopStmt) = true

#guard
  smokeSome
    (Stmt.toFunctionsListFuel? 16
      (Fresh.initial (Stmt.names smokeReturnStmt))
      smokeReturnStmt) = true

#guard
  smokeSome
    (Stmt.toFunctionsListFuel? 16
      (Fresh.initial (Stmt.names smokeRevertStmt))
      smokeRevertStmt) = true

#guard
  smokeSome
    (Stmt.toFunctionsListFuel? 16
      (Fresh.initial (Stmt.names smokeSelfdestructStmt))
      smokeSelfdestructStmt) = true

#guard
  smokeSome
    (Expr.lower1? (Fresh.initial (Expr.names smokeExternalCallExpr))
      smokeExternalCallExpr) = true

#guard
  smokeSome
    (Expr.lower1? (Fresh.initial (Expr.names smokeExternalCallcodeExpr))
      smokeExternalCallcodeExpr) = true

#guard
  smokeSome
    (Expr.lower1? (Fresh.initial (Expr.names smokeExternalStaticCallExpr))
      smokeExternalStaticCallExpr) = true

#guard
  smokeSome
    (Expr.lower1? (Fresh.initial (Expr.names smokeExternalDelegateCallExpr))
      smokeExternalDelegateCallExpr) = true

#guard
  Expr.lower1? (Fresh.initial (Expr.names smokeGasExpr)) smokeGasExpr = none

#guard
  Prim.toUncheckedBasicOp?
      ((.StackMemFlow .GAS : EvmYul.Operation .Yul)) = some .gas

#guard
  smokeSome
    (Expr.lower1Unchecked? (Fresh.initial (Expr.names smokeGasExpr))
      smokeGasExpr) = true

#guard
  smokeSome
    smokeWideUncheckedFunctionsProgram? = true

#guard
  smokeSome
    (smokeWideUncheckedFunctionsProgram? >>=
      Functions.Program.toLocals?) = true

#guard
  smokeSome
    (smokeWideUncheckedFunctionsProgram? >>=
      Functions.Program.toExpressions?) = true

#guard
  smokeSome
    (smokeWideUncheckedFunctionsProgram? >>=
      Functions.Program.compile?) = true

#guard
  Expr.pendingStackDepth (smokeDeepPureAliasExpr 16) = 16

#guard
  Expr.List.directPureArgsSafe? [smokeDeepPureAliasExpr 16] = false

#guard
  smokeDeepPureAliasMaterializes = true

#guard
  smokeShallowPureAliasStaysDirect = true

#guard
  smokeSome
    (Expr.lower1? (Fresh.initial (Expr.names smokeCreateExpr))
      smokeCreateExpr) = true

#guard
  smokeSome
    (Expr.lower1? (Fresh.initial (Expr.names smokeCreate2Expr))
      smokeCreate2Expr) = true

#guard
  smokeSome
    (Expr.lower1? (Fresh.initial (Expr.names smokeBalanceExpr))
      smokeBalanceExpr) = true

#guard
  smokeSome
    (Expr.lower1? (Fresh.initial (Expr.names smokeExtcodesizeExpr))
      smokeExtcodesizeExpr) = true

#guard
  smokeSome
    (Expr.lower1? (Fresh.initial (Expr.names smokeExtcodehashExpr))
      smokeExtcodehashExpr) = true

#guard
  smokeSome
    (Stmt.toFunctionsListFuel? 16
      (Fresh.initial (Stmt.names smokeExtcodecopyStmt))
      smokeExtcodecopyStmt) = true

#guard
  (match
      smokeObjectProgram.object.toYulProgramWithLocalDataBase?
        smokeObjectLayout 64 with
  | some program =>
      match program.contract.dispatcher with
      | .Block
          [ .Let ["size"] (some (.Lit size))
          , .Let ["offset"] (some (.Lit offset))
          , .Let ["guard"] (some (.Lit guard))
          , .ExprStmtCall
              (.Call (.inl ((.Env .CODECOPY : EvmYul.Operation .Yul)))
                [.Lit target, .Lit copyOffset, .Lit copySize]) ] =>
            size.toNat == smokeObjectDataBytes.length &&
              offset.toNat == 64 &&
              guard.toNat == 128 &&
              target.toNat == 0 &&
              copyOffset.toNat == 64 &&
              copySize.toNat == smokeObjectDataBytes.length
      | _ => false
  | none => false) = true

#guard
  (match
      Solidity.Frontend.Expr.resolveObjectBuiltinsIn?
        (.call .objectBuiltin "linkersymbol" [.stringLit "LIB"])
        smokeObjectContext >>= Solidity.Frontend.Expr.toYul? with
  | some (.Lit value) => value.toNat == smokeOne.toNat
  | _ => false) = true

#guard
  (match
      Solidity.Frontend.Expr.resolveObjectBuiltinsIn?
        (.call .objectBuiltin "datasize" [.bytesLit smokeObjectNameBytes])
        smokeObjectContext >>= Solidity.Frontend.Expr.toYul? with
  | some (.Lit value) => value.toNat == smokeObjectDataBytes.length
  | _ => false) = true

#guard
  (match
      Solidity.Frontend.Expr.resolveObjectBuiltinsIn?
        (.call .objectBuiltin "dataoffset" [.bytesLit smokeObjectNameBytes])
        smokeObjectContext >>= Solidity.Frontend.Expr.toYul? with
  | some (.Lit value) => value.toNat == 64
  | _ => false) = true

#guard
  (match
      Solidity.Frontend.Expr.resolveObjectBuiltinsIn?
        (.call .objectBuiltin "linkersymbol"
          [.bytesLit smokeLinkerSymbolNameBytes])
        smokeObjectContext >>= Solidity.Frontend.Expr.toYul? with
  | some (.Lit value) => value.toNat == smokeOne.toNat
  | _ => false) = true

#guard
  Solidity.Frontend.Expr.loadImmutableNames
      (.call .objectBuiltin "loadimmutable"
        [.bytesLit smokeImmutableNameBytes]) =
    ["IMM"]

#guard
  (match
      Solidity.Frontend.Expr.resolveObjectBuiltinsIn?
        (.call .objectBuiltin "loadimmutable"
          [.bytesLit smokeImmutableNameBytes])
        smokeImmutableContext >>= Solidity.Frontend.Expr.toYul? with
  | some (.Lit value) => value.toNat == smokeOne.toNat
  | _ => false) = true

#guard
  (match
      Solidity.Frontend.Stmt.resolveObjectBuiltinsIn?
        (.exprStmt
          (.call .objectBuiltin "setimmutable"
            [ .var "base"
            , .bytesLit smokeImmutableNameBytes
            , .lit smokeOne ]))
        smokeSetImmutableContext with
  | some
      (.block
        [ .exprStmt
            (.call .primitive "mstore"
              [ .call .primitive "add"
                  [.var "base", .lit offset]
              , .lit value ]) ]) =>
      offset.toNat == 7 && value.toNat == smokeOne.toNat
  | _ => false) = true

#guard
  (match
      Solidity.Frontend.Stmt.resolveObjectBuiltinsIn?
        (.exprStmt
          (.call .objectBuiltin "setimmutable"
            [ .var "base"
            , .bytesLit smokeImmutableNameBytes
            , .lit smokeOne ]))
        smokeSetImmutableNoReferenceContext with
  | some (.block []) => true
  | _ => false) = true

end

end Yul
end EvmCompiler
