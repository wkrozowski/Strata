/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

/-!
# Tests for the proof-producing SMT translation

For each query, `gen_smt_vcs` translates it with `translateQuery` and proves
with `Strata.SMT.ProofGen.proveQuery` that the translation is the query's
denotation. These tests run both on one query per supported construct and
kernel-check the resulting theorem `denoteQuery ctx ts t = some P`.
-/

open Lean (Expr mkApp mkApp2 mkApp3 addDecl Declaration logInfo toExpr getEnv)
open Lean.Meta
open Strata Strata.SMT

namespace Strata.DenoteProofTests
abbrev B := TermType.prim .bool
abbrev I := TermType.prim .int
abbrev S := TermType.prim .string
def BV (n : Nat) : TermType := .prim (.bitvec n)
def c (n : String) (ty : TermType) : SMT.Term := .app (.uf ⟨n, [], ty⟩) [] ty
def ap (o : Op) (as : List SMT.Term) (ty : TermType) : SMT.Term := .app o as ty
def bv (n : Nat) (k : Nat) : SMT.Term := .prim (.bitvec (BitVec.ofNat n k))
def eq (a b : SMT.Term) : SMT.Term := ap .eq [a, b] B
def ctxOf (ufs : List UF) (sorts : List Strata.DL.SMT.Sort := []) (tySubst : Map String TermType := []) : SanitizedContext :=
  { ufs := ufs.toArray, sorts := sorts.toArray, tySubst }
def x8 := c "x" (BV 8)
def y8 := c "y" (BV 8)
def u8 : List UF := [⟨"x", [], BV 8⟩, ⟨"y", [], BV 8⟩]
def Arr := TermType.constr "Array" [I, I]

def cases : List (String × SanitizedContext × List SMT.Term × SMT.Term) := [
  ("bvlit", ctxOf [], [], eq (bv 8 3) (bv 8 3)),
  ("bvneg", ctxOf u8, [], eq (ap .bvneg [x8] (BV 8)) y8),
  ("bvnot", ctxOf u8, [], eq (ap .bvnot [x8] (BV 8)) y8),
  ("bvnego", ctxOf u8, [], ap .bvnego [x8] B),
  ("bvadd3", ctxOf u8, [], eq (ap .bvadd [x8, y8, x8] (BV 8)) y8),
  ("bvsub", ctxOf u8, [], eq (ap .bvsub [x8, y8] (BV 8)) y8),
  ("bvmul", ctxOf u8, [], eq (ap .bvmul [x8, y8] (BV 8)) y8),
  ("bvand", ctxOf u8, [], eq (ap .bvand [x8, y8] (BV 8)) y8),
  ("bvor", ctxOf u8, [], eq (ap .bvor [x8, y8] (BV 8)) y8),
  ("bvxor", ctxOf u8, [], eq (ap .bvxor [x8, y8] (BV 8)) y8),
  ("bvshl", ctxOf u8, [], eq (ap .bvshl [x8, y8] (BV 8)) y8),
  ("bvlshr", ctxOf u8, [], eq (ap .bvlshr [x8, y8] (BV 8)) y8),
  ("bvashr", ctxOf u8, [], eq (ap .bvashr [x8, y8] (BV 8)) y8),
  ("bvslt", ctxOf u8, [], ap .bvslt [x8, y8] B),
  ("bvsle", ctxOf u8, [], ap .bvsle [x8, y8] B),
  ("bvult", ctxOf u8, [], ap .bvult [x8, y8] B),
  ("bvsge", ctxOf u8, [], ap .bvsge [x8, y8] B),
  ("bvsgt", ctxOf u8, [], ap .bvsgt [x8, y8] B),
  ("bvule", ctxOf u8, [], ap .bvule [x8, y8] B),
  ("bvugt", ctxOf u8, [], ap .bvugt [x8, y8] B),
  ("bvuge", ctxOf u8, [], ap .bvuge [x8, y8] B),
  ("bvudiv", ctxOf u8, [], eq (ap .bvudiv [x8, y8] (BV 8)) y8),
  ("bvurem", ctxOf u8, [], eq (ap .bvurem [x8, y8] (BV 8)) y8),
  ("bvsdiv", ctxOf u8, [], eq (ap .bvsdiv [x8, y8] (BV 8)) y8),
  ("bvsrem", ctxOf u8, [], eq (ap .bvsrem [x8, y8] (BV 8)) y8),
  ("bvsaddo", ctxOf u8, [], ap .bvsaddo [x8, y8] B),
  ("bvssubo", ctxOf u8, [], ap .bvssubo [x8, y8] B),
  ("bvsmulo", ctxOf u8, [], ap .bvsmulo [x8, y8] B),
  ("bvconcat", ctxOf u8, [], eq (ap .bvconcat [x8, y8] (BV 16)) (ap .bvconcat [y8, x8] (BV 16))),
  ("zero_extend", ctxOf u8, [], eq (ap (.zero_extend 8) [x8] (BV 16)) (ap (.zero_extend 8) [y8] (BV 16))),
  ("ubv_to_int", ctxOf u8, [], ap .le [ap .ubv_to_int [x8] I, .prim (.int 255)] B),
  ("sbv_to_int", ctxOf u8, [], ap .le [ap .sbv_to_int [x8] I, .prim (.int 127)] B),
  ("int_to_bv", ctxOf (u8 ++ [⟨"n", [], I⟩]), [], eq (ap (.int_to_bv 8) [c "n" I] (BV 8)) x8),
  ("bvquant", ctxOf u8, [], .quant .all [⟨"z", BV 8⟩] [] (eq (ap .bvadd [.var ⟨"z", BV 8⟩, x8] (BV 8)) y8)),
  ("strlit", ctxOf [⟨"s", [], S⟩], [], eq (c "s" S) (.prim (.string "hello"))),
  ("strlen", ctxOf [⟨"s", [], S⟩], [], ap .ge [ap .str_length [c "s" S] I, .prim (.int 0)] B),
  ("strconcat", ctxOf [⟨"s", [], S⟩], [], eq (ap .str_concat [c "s" S, .prim (.string "a"), c "s" S] S) (c "s" S)),
  ("select", ctxOf [⟨"a", [], Arr⟩], [], eq (ap .select [c "a" Arr, .prim (.int 1)] I) (.prim (.int 2))),
  ("store", ctxOf [⟨"a", [], Arr⟩], [],
    eq (ap .select [ap .store [c "a" Arr, .prim (.int 1), .prim (.int 2)] Arr, .prim (.int 1)] I) (.prim (.int 2))),
  ("arrayfun", ctxOf [⟨"a", [], Arr⟩, ⟨"g", [Arr], I⟩], [],
    eq (.app (.uf ⟨"g", [Arr], I⟩) [ap .store [c "a" Arr, .prim (.int 1), .prim (.int 2)] Arr] I) (.prim (.int 0))),
  ("none", ctxOf [⟨"o", [], .option I⟩], [], eq (c "o" (.option I)) (.none I)),
  ("some", ctxOf [⟨"o", [], .option I⟩], [], eq (c "o" (.option I)) (.some (.prim (.int 3)))),
  ("abs", ctxOf [⟨"n", [], I⟩], [], ap .ge [ap .abs [c "n" I] I, .prim (.int 0)] B),
  ("synonym", ctxOf [⟨"m", [], .constr "MyInt" []⟩] [] [("MyInt", I)], [],
    ap .ge [c "m" (.constr "MyInt" []), .prim (.int 0)] B),
  ("synonym_sort", ctxOf [⟨"p", [], .constr "P" []⟩, ⟨"q", [], .constr "P" []⟩] [⟨"T", 0⟩] [("P", .constr "T" [])], [],
    eq (c "p" (.constr "P" [])) (c "q" (.constr "P" []))),
  ("synonym_bv", ctxOf [⟨"w", [], .constr "Word" []⟩] [] [("Word", BV 8)], [],
    eq (ap .bvadd [c "w" (.constr "Word" []), bv 8 1] (BV 8)) (c "w" (.constr "Word" []))),
  -- Declarations that share a name but not a type: the lookup in `denoteTerm`
  -- compares the whole declaration, so it skips the inner `x : Bool` (resp.
  -- `f : Bool → Bool`) when resolving `x : Int` (resp. `f : Int → Int`).
  ("shadow_var", ctxOf [], [],
    .quant .all [⟨"x", I⟩] [] (.quant .all [⟨"x", B⟩] [] (ap .ge [.var ⟨"x", I⟩, .prim (.int 0)] B))),
  ("overload_uf", ctxOf [⟨"f", [I], I⟩, ⟨"f", [B], B⟩], [],
    ap .and [ap .ge [.app (.uf ⟨"f", [I], I⟩) [.prim (.int 1)] I, .prim (.int 0)] B,
             .app (.uf ⟨"f", [B], B⟩) [.prim (.bool true)] B] B)
]
end Strata.DenoteProofTests

/-- info: 48/48 kernel-checked -/
#guard_msgs in
run_meta do
  let mut ok := 0
  for (label, sc, ts, t) in Strata.DenoteProofTests.cases do
    let (sc0, ts0, t0) := SMT.substituteSynonyms sc ts t
    match translateQuery sc0.toCore ts0 t0 with
    | .error e => logInfo m!"{label}: translateQuery failed: {e}"
    | .ok P =>
      try
        let (Pj, pf) ← SMT.ProofGen.proveQuery sc (toExpr sc) ts (toExpr ts) t (toExpr t)
        unless (Lean.Kernel.isDefEq (← getEnv) {} Pj P matches .ok true) do
          throwError "denotation does not match translation"
        let ty := mkApp3 (.const ``Eq [1]) (mkApp (.const ``Option [0]) (.sort 0))
          (mkApp3 (.const ``denoteQuery []) (mkApp (.const ``Strata.SMT.SanitizedContext.toCore []) (toExpr sc)) (toExpr ts) (toExpr t))
          (mkApp2 (.const ``Option.some [0]) (.sort 0) P)
        addDecl (.thmDecl { name := `Strata.DenoteProofTests.thm ++ label.toName, levelParams := [], type := ty, value := pf })
        ok := ok + 1
      catch e => logInfo m!"{label}: FAIL {e.toMessageData}"
  logInfo m!"{ok}/{Strata.DenoteProofTests.cases.length} kernel-checked"

/-! A query whose translation is not its denotation is rejected: `translateQuery`
reads a one-operand implication as its operand, but its denotation is `none`. -/

/-- info: proveQuery: implication needs at least two operands -/
#guard_msgs in
run_meta do
  let t : Strata.SMT.Term := .app .implies [.prim (.bool true)] (.prim .bool)
  let sc : Strata.SMT.SanitizedContext := {}
  try
    let _ ← Strata.SMT.ProofGen.proveQuery sc (toExpr sc) [] (toExpr ([] : List Strata.SMT.Term)) t (toExpr t)
    logInfo "unexpectedly proved"
  catch e => logInfo e.toMessageData
