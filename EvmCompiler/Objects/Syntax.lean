import EvmCompiler.Functions.Syntax

namespace EvmCompiler
namespace Objects

abbrev Word := Functions.Word
abbrev EVMState := Functions.EVMState
abbrev EVMException := Functions.EVMException
abbrev Name := Functions.Name

structure DataSection where
  name? : Option Name
  bytes : List UInt8

inductive Object where
  | mk (name : Name) (code : Functions.Program)
      (data : List DataSection) (objects : List Object)

namespace Object

def name : Object → Name
  | .mk name _code _data _objects => name

def code : Object → Functions.Program
  | .mk _name code _data _objects => code

def data : Object → List DataSection
  | .mk _name _code data _objects => data

def objects : Object → List Object
  | .mk _name _code _data objects => objects

def toFunctions (object : Object) : Functions.Program :=
  object.code

end Object

mutual
  def Object.WF : Object → Prop
    | .mk _name code _data objects =>
        code.WF ∧ ObjectList.WF objects

  def ObjectList.WF : List Object → Prop
    | [] => True
    | object :: rest =>
        object.WF ∧ ObjectList.WF rest
end

structure Program where
  root : Object

namespace Program

def toFunctions (program : Program) : Functions.Program :=
  program.root.toFunctions

def withMemoryContract (program : Program)
    (memoryContract : MemoryContract.Contract) : Program :=
  match program.root with
  | .mk name code data objects =>
      { root :=
          .mk name { code with memoryContract := memoryContract }
            data objects }

@[simp] theorem toFunctions_withMemoryContract
    (program : Program)
    (memoryContract : MemoryContract.Contract) :
    (program.withMemoryContract memoryContract).toFunctions =
      { program.toFunctions with memoryContract := memoryContract } := by
  cases program with
  | mk root =>
      cases root
      rfl

def WF (program : Program) : Prop :=
  program.root.WF

end Program

end Objects
end EvmCompiler
