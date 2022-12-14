import Straume.Zeptoparsec

import Wasm.Wast.BitSize
import Wasm.Wast.Name
import Wasm.Wast.Num
import Wasm.Wast.Parser.Common

import YatimaStdLib

open Wasm.Wast.Name
open Wasm.Wast.Parser.Common
open Wasm.Wast.Num.Num.Int
open Wasm.Wast.Num.Num.Float

open Zeptoparsec

namespace Wasm.Wast.Code

namespace Type'

inductive Type' where
| f : BitSize → Type'
| i : BitSize → Type'
-- | v : BitSizeSIMD → Type'
  deriving BEq

instance : ToString Type' where
  toString x := match x with
  | .f y => "(Type'.f " ++ toString y ++ ")"
  | .i y => "(Type'.i " ++ toString y ++ ")"
  -- | .v y => "(Type'.v " ++ toString y ++ ")"

def typeP : Parsec String Type' := do
  let iorf ← (pstring "i" <|> pstring "f")
  let bits ← bitSizeP
  match iorf with
  | "i" => pure $ Type'.i bits
  | "f" => pure $ Type'.f bits
  | _ => fail $ "Expected type string, got something else."

end Type'

namespace Local

open Name
open Type'

structure Local where
  index : Nat
  name : Option String
  type : Type' -- TODO: We need to pack lists with different related types'. For that we need something cooler than List, but since we're just coding now, we'll do it later.
  deriving BEq

instance : ToString Local where
  toString x := s!"(Local.mk {x.index} {x.type})"

end Local

namespace Get

open Type'
open Local

inductive Get (x : Type') where
| from_stack
| by_name : Local → Get x
| by_index : Local → Get x
-- TODO: replace "Unit" placeholder with ConstVec when implemented
-- TODO: generalise Consts the same way Get is generalised so that Get' i32 can't be populated with ConstFloat!
| const : (ConstInt ⊕ ConstFloat ⊕ Unit) → Get x

instance : ToString (Get α) where
  toString x := "(" ++ (
    match x with
    | .from_stack => "Get.from_stack"
    | .by_name n => "Get.by_name " ++ toString n
    | .by_index i => "Get.by_index " ++ toString i
    | .const ifu => "Get.const " ++ (match ifu with
      | .inl i => "(Sum.inl " ++ toString i ++ ")"
      | .inr $ .inl f => "(Sum.inr $ Sum.inl " ++ toString f ++ ")"
      | .inr $ .inr () => sorry
    )
  ) ++ " : Get " ++ toString α ++ ")"

def getConstP : Parsec String (Get x) := do
  dbg_trace ">>>>>>>>> GET CONST P <<<<<<<<<"
  let _ ← pstring "("
  dbg_trace "oOoO(1)OoOo"
  let resP := match x with
    | .i 32 => i32P >>= fun y => pure $ Get.const $ .inl y
    | .i 64 => i64P >>= fun y => pure $ Get.const $ .inl y
    | .f 32 => f32P >>= fun y => pure $ Get.const $ .inr $ .inl y
    | .f 64 => f64P >>= fun y => pure $ Get.const $ .inr $ .inl y
  -- TODO: Understand why this bind fixed things!
  let y ← resP
  dbg_trace s!"oOoO({y})OoOo"
  let _ ← pstring ")"
  dbg_trace "-=-=<*>=-=-"
  pure y

def getP : Parsec String (Get x) := do
  dbg_trace "<<<<<<< GET P! >>>>>>>>"
  -- TODO: implement locals!!!
  getConstP <|> (pure $ Get.from_stack)

end Get

namespace Instruction

/- TODO: Instructions are rigid WAT objects. If we choose to only support
S-Expressions at this point, we don't need this concept. -/

end Instruction

namespace Operation

open Type'
open Get
open Local

mutual
  -- Sadge
  inductive Get' where
  | from_stack
  | from_operation : Operation → Get'
  | by_name : Local → Get'
  | by_index : Local → Get'
  | i_const : ConstInt → Get'
  | f_const : ConstFloat → Get'

  inductive Add' where
  | add : Type' → Get' → Get' → Add'

  inductive Operation where
  | add : Add' → Operation
end

mutual
  partial def getToString (x : Get') : String :=
    "(Get'" ++ (
      match x with
      | .from_stack => ".from_stack"
      | .from_operation o => s!".from_operation {operationToString o}"
      | .by_name n => ".by_name " ++ toString n
      | .by_index i => ".by_index " ++ toString i
      | .i_const i => s!".i_const {i}"
      | .f_const f => s!".f_const {f}"
    ) ++ ")"

  partial def operationToString : Operation → String
    | ⟨y⟩ => s!"(Operation.add {addToString y})"

  partial def addToString : Add' → String
    | ⟨t, g1, g2⟩ => s!"(Add'.add {t} {getToString g1} {getToString g2})"
end

instance : ToString Add' where
  toString := addToString

instance : ToString Get' where
  toString := getToString

instance : ToString Operation where
  toString := operationToString

def stripGet (α : Type') (x : Get α) : Get' :=
  match x with
  | .from_stack => Get'.from_stack
  | .by_name n => Get'.by_name n
  | .by_index i => Get'.by_index i
  | .const ifu => match ifu with
    | .inl i => Get'.i_const i
    | .inr $ .inl f => Get'.f_const f
    | _ => sorry

mutual

  partial def get'ViaGetP (α  : Type') : Parsec String Get' :=
    attempt
      (opP >>= (pure ∘ Get'.from_operation)) <|>
      (getP >>= (pure ∘ stripGet α))

  partial def opP : Parsec String Operation := do
    dbg_trace "]]]] We're parsing operation [[[["
    let add ← addP
    dbg_trace "]]]] {add} [[[["
    pure $ Operation.add add

  partial def opsP : Parsec String (List Operation) := do
    dbg_trace "TRYING TO PARSE OPS"
    sepEndBy' opP owP

  partial def addP : Parsec String Add' := do
    cbetween '(' ')' do
      dbg_trace ">>>>>> Running addP"
      owP
      dbg_trace ">>>>>> 1"
      -- TODO: we'll use ps when we'll add more types into `Type'`.
      -- let _ps ← getParserState
      let add_t : Type' ←
        pstring "i32.add" *> (pure $ .i 32) <|>
        pstring "i64.add" *> (pure $ .i 64) <|>
        pstring "f32.add" *> (pure $ .f 32) <|>
        pstring "f64.add" *> (pure $ .f 64)
      dbg_trace s!">>>>>> {add_t} IGNORING"
      ignoreP
      dbg_trace ">>>>>> IGNORED"
      let (arg_1 : Get') ← get'ViaGetP add_t
      dbg_trace s!">>>>>> GOT! {arg_1}"
      owP
      let (arg_2 : Get') ← get'ViaGetP add_t
      dbg_trace s!">>>>>> GOT! {arg_2}"
      owP
      pure $ Add'.add add_t arg_1 arg_2
end

end Operation

namespace Func

open Name
open Type'
open Local
open Operation

structure Func where
  name : Option String
  export_ : Option String
  -- TODO: Heterogenous lists so that we can promote Type'?
  params : List Local
  result : List Type'
  locals : List Local
  ops : List Operation

instance : ToString Func where
  toString x := s!"(Func.mk {x.name} {x.export_} {x.params} {x.result} {x.locals} {x.ops})"

def exportP : Parsec String String := do
  cbetween '(' ')' do
    discard $ pstring "export"
    ignoreP
    -- TODO: are escaped quotation marks legal export names?
    let export_label ← cbetween '\"' '\"' $ many $ noneOf "\"".data
    pure $ String.mk $ Array.toList export_label

def genLocalP (x : String) : Parsec String Local := do
  discard $ pstring x
  -- TODO: We moved from `option'` to `option` here. Did we just wrote a bug?
  dbg_trace "Beep {x}"
  let olabel ← (option ∘ attempt) (ignoreP *> nameP)
  dbg_trace "Boop {x}"
  let typ ← ignoreP *> typeP
  dbg_trace "Doop {x} : {typ}"
  pure $ match olabel with
  | .none =>
    dbg_trace ">>: {typ} :<<"
    Local.mk 0 .none typ
  | .some l =>
    dbg_trace ">>: {l} {typ} :<<"
    Local.mk 0 (.some l) typ

def paramP : Parsec String Local := do
  dbg_trace ">>:>> param <<:<<"
  let y := genLocalP "param"
  dbg_trace ">>:>> param1 <<:<<"
  y

def localP : Parsec String Local :=
  genLocalP "local"

def manyLispP (p : Parsec String α) : Parsec String (List α) :=
  sepEndBy' (attempt $ single '(' *> owP *> p <* owP <* single ')') owP

def nilParamsP : Parsec String (List Local) := do
  manyLispP paramP

def nilLocalsP : Parsec String (List Local) :=
  manyLispP localP

def reindexLocals (start : Nat := 0) (ps : List Local) : List Local :=
  (ps.foldl (
      fun acc x =>
        (acc.1 + 1, {x with index := acc.1} :: acc.2)
    ) (start, [])
  ).2.reverse

def resultP : Parsec String Type' := do
  dbg_trace "RESULT!"
  let _ ← pstring "result"
  dbg_trace "IGNORE!"
  ignoreP
  dbg_trace "IGNORED!"
  let x ← typeP
  dbg_trace s!"RESULT {x}"
  pure x

def brResultP : Parsec String Type' :=
  single '(' *> owP *> resultP <* owP <* single ')'

def brResultsP : Parsec String (List Type') :=
  manyLispP resultP

def funcP : Parsec String Func := do
  cbetween '(' ')' do
    owP <* (pstring "func")
    -- let oname ← option' (ignoreP *> nameP)
    let oname ← option (attempt $ ignoreP *> nameP)
    let oexp ← option (attempt $ owP *> exportP)
    let ops ← option (attempt $ owP *> nilParamsP)
    let ps := optional ops []
    let ps := reindexLocals 0 ps
    let psn := ps.length
    let rtypes ← attempt $ owP *> brResultsP
    let ols ← option (attempt $ owP *> nilLocalsP)
    let ls := reindexLocals psn $ optional ols []
    let oops ← option (attempt $ owP *> opsP)
    let ops := optional oops []
    owP
    pure $ Func.mk oname oexp ps rtypes ls ops

def reindexParamsAndLocals (f : Func) : (List Local × List Local) :=
  let ps := reindexLocals 0 f.params
  let ls := reindexLocals (ps.length) f.locals
  (ps, ls)

end Func

namespace Module

/-

(module $target
    (func)
    (func $f (export "(module (func))") (param $y f32) (param $y1 f32) (result f32)
        (local $dummy i32)
        (i32.const 42)
        (local.set 2)
        (local.get $y1)
        (f32.add (local.get $y1))
        (local.get $y)
        (f32.add)
    )
    (func (export "main") (result f32)
        (local $x f32) (local $y f32)
        (local.set $x (f32.const 0.1))
        (local.set $y (f32.const 20.95))
        (call $f (local.get $x) (local.get $y))
    )
)

-/

open Name
open Type'
open Func
open Operation

structure Module where
  name : Option String
  func : List Func

instance : ToString Module where
  toString x := s!"(Module.mk {x.name} {x.func})"

def moduleP : Parsec String Module := do
  cbetween '(' ')' do
    owP <* (pstring "module")
    let oname ← option (attempt $ ignoreP *> nameP)
    let ofuns ← option (attempt $ ignoreP *> sepEndBy' funcP owP)
    let funs := optional ofuns []
    owP
    pure $ Module.mk oname funs

end Module

namespace Block
end Block

namespace Loop
end Loop
