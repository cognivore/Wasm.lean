import LSpec
import Megaparsec.Parsec
import Wasm.Wast.Parser
import Wasm.Bytes
import Wasm.Tests

open LSpec
open Megaparsec.Parsec
open Wasm.Wast.Parser
open Wasm.Bytes
open Wasm.Tests

/-! To test runtime compatibility between Wasm.lean engine and the reference
implementation, we choose to constrain ourselves to running only `() -> I32`
Wasm functions.
Note that our engine encodes it as `Int`, not `UInt32` at the moment.

Some discussion about this design choice can be read here:
https://github.com/yatima-inc/Wasm.lean/pull/53
 -/

partial def testGeneric : String → Int → Int → TestSeq
  | mod, os, rs =>
    let str := s!"Running function _main_ : () -> I32 evaluates the same in Lean and Rust.
    {mod}
    ! If failed, remember: first is ours, second is rust) !"
    test str $ os = rs

open IO.FS in
partial def runWasmTestSeq (x : String) : IO TestSeq := do
  match ←run_main x with
  | .ok y => do
    let yᵢ := y.trim.toInt!
    match parseP moduleP "test" x with
    | .error pe => pure $ test "parsing module" (ParseFailure x pe)
    | .ok m => match runModule m with
      | .ok our_y => pure $ testGeneric x our_y yᵢ
      | .error ee => pure $ test "running module" (EngineFailure x ee)
  | .error e =>
    pure $ test s!"failed to run with wasm-sandbox: {x}" (ExternalFailure e)

def basics :=
  [ "(module
        (func (export \"main\") (result i32)
          (i32.const 3555)
        )
     )"
  ]

def supported := [

  "(module ;;deep
        (func (export \"main\") (result i32)
          (block (result i32) (block (result i32)
            (block (result i32) (block (result i32)
              (block (result i32) (block (result i32)
                (block (result i32) (block (result i32)
                  (block (result i32) (block (result i32)
                    (block (result i32) (block (result i32)
                      (block (result i32) (block (result i32)
                        (block (result i32) (block (result i32)
                          (block (result i32) (block (result i32)
                            (block (result i32) (block (result i32)
                              (block (result i32) (block (result i32)
                                (block (result i32) (block (result i32)
                                  (block (result i32) (block (result i32)
                                    (block (result i32) (block (result i32)
                                      (block (result i32) (block (result i32)
                                        (block (result i32) (block (result i32)
                                          (block (result i32) (block (result i32)
                                            (block (result i32) (block (result i32)
                                              (block (result i32) (block (result i32)
                                                ;; (nop) (i32.const 150)
                                                (i32.const 150)
                                              ))
                                            ))
                                          ))
                                        ))
                                      ))
                                    ))
                                  ))
                                ))
                              ))
                            ))
                          ))
                        ))
                      ))
                    ))
                  ))
                ))
              ))
            ))
          ))
    )
)",

"(module (func (export \"main\") (result i32)
  (block (nop))
  (block (result i32) (i32.const 7))
))",

"(module (func (export \"main\") (result i32)
  (block (nop) (nop) (nop) (nop))
  (block (result i32)
    (nop) (nop) (nop) (i32.const 7) (nop)
  )
  (drop)
  (block (result i32 i64 i32)
    (nop) (nop) (nop) (i32.const 8) (nop)
    (nop) (nop) (nop) (i64.const 7) (nop)
    (nop) (nop) (nop) (i32.const 9) (nop)
  )
  (drop) (drop)
))",

"(module (func (export \"main\") (result i32)
  (block (result i32)
    (block (nop) (block) (nop))
    (block (result i32) (nop) (i32.const 9))
  )
))",

"(module (func (export \"main\") (result i32) ;; empty
  (block)
  (block $l)
  (i32.const 0)
))",

"(module (func (export \"main\") (result i32)
  (select (block (result i32) (i32.const 1)) (i32.const 2) (i32.const 3))
))",
"(module (func (export \"main\") (result i32)
  (select (i32.const 2) (block (result i32) (i32.const 1)) (i32.const 3))
))",
"(module (func (export \"main\") (result i32)
  (select (i32.const 2) (i32.const 3) (block (result i32) (i32.const 1)))
))",

"(module (func (export \"main\") (result i32)
  (loop (result i32) (block (result i32) (i32.const 1)) (nop) (nop))
))",
"(module (func (export \"main\") (result i32)
  (loop (result i32) (nop) (block (result i32) (i32.const 1)) (nop))
))",
"(module (func (export \"main\") (result i32)
  (loop (result i32) (nop) (nop) (block (result i32) (i32.const 1)))
))",

"(module (func (export \"main\") (result i32)
  (if (result i32) (i32.const 1) (then (block (result i32) (i32.const 1))) (else (i32.const 2)))
))",
"(module (func (export \"main\") (result i32)
  (if (result i32) (i32.const 1) (then (i32.const 2)) (else (block (result i32) (i32.const 1))))
))",

"(module (func (export \"main\") (result i32)
  (block (result i32) (br_if 0 (block (result i32) (i32.const 1)) (i32.const 2)))
))",
"(module (func (export \"main\") (result i32)
  (block (result i32) (br_if 0 (i32.const 2) (block (result i32) (i32.const 1))))
))",

"(module (func (export \"main\") (result i32)
  (block (result i32) (block (result i32) (i32.const 1)) (i32.const 2) (br_table 0 0))
))",
"(module (func (export \"main\") (result i32)
  (block (result i32) (i32.const 2) (block (result i32) (i32.const 1)) (br_table 0 0))
))"

]

def main : IO UInt32 := do
  match (← doesWasmSandboxRun?) with
  | .ok _ => withWasmSandboxRun runWasmTestSeq [ basics, supported ]
  | _ => withWasmSandboxFail
