# Proof-producing `gen_smt_vcs`

This change removes the per-theorem TCB bridge axiom that `gen_smt_vcs`
introduced in #1453, following recommendation 2 of issue #1442: instead of
trusting `translateQuery`, the tactic now *proves* that each goal it creates is
the denotation (`denoteQuery`) of the corresponding verification condition.

## Background: what broke on Lean 4.31

Before #1453, `gen_smt_vcs` assigned the goal `(denoteQueries vcs).getD False`
a proof of the conjunction of the `translateQuery` goals and relied on the
kernel to check, by unfolding `denoteQueries`, `denoteQuery`, `denoteTerm`,
`bindUF`, … on the concrete VCs, that the two are definitionally equal.

The failure was mostly a module-system issue rather than a change to matcher
reduction: in a `module` file the kernel cannot see the bodies of non-exposed
definitions (`denoteQuery`, `denoteBoolTermFromContext`, `bindUF`, …), so the
implicit definitional equality fails with the opaque "failed to pretty print"
type mismatch. In non-module files the old approach still kernel-checks on
4.31 (including at the commit before #1453).

## How it works now

For each VC, `gen_smt_vcs`:

1. builds the goal `P` with `translateQuery` (unchanged, still untrusted);
2. builds a proof of `denoteQuery sc.toCore ts t = some P'` by chaining
   lemmas from `Strata.SMT.DenoteLemmas` along the structure of the term
   (`Strata.SMT.ProofGen.proveQuery`);
3. checks with `Lean.Kernel.isDefEq` that `P'` and `P` agree. This only needs
   beta reduction, projections, list lookups and casts over exposed
   sort-level definitions — never unfolding of the denotation itself;
4. combines the per-VC proofs with `denoteQueries_cons`/`_go_cons` and closes
   `smtVCsCorrect` with `smtVCsCorrect_of`.

The only remaining trusted step is the existing `native_decide` proof that
`genSMTVCs program options` evaluates to the VC list (`Lean.ofReduceBool`).

If step 2 or 3 fails for a VC, the tactic reports an error naming it. There is
no option to trust the translation instead: a per-VC axiom stating the
equation can be false (e.g. when the translation exists but `denoteQuery` is
`none`, as for a one-operand `implies`), and would then prove `False`.

The tactic also works inside `module` files now; on `main` it could not even
unfold `smtVCsCorrect` there.

### Lemma style

Lemmas are stated in "hypothesis style": the denotations of subterms are
hypotheses and the conclusion gives the parent's semantic function, e.g.

```lean
theorem den_not (ctx a rt h fa)
    (ha : denoteTerm ctx a = some ⟨.prim .bool, h, fa⟩) :
    denoteTerm ctx (.app .not [a] rt) = some ⟨.prim .bool, h, fun Γ => ¬ fa Γ⟩
```

Conclusions only mention constants whose bodies importers can see, so the
composed semantic function reduces to the translated proposition. Non-exposed
helpers that do appear in `denoteTerm`'s output (`applyUF`, `buildForall`,
`buildIFBody`, `leftAssoc.go`, …) are eliminated by equation lemmas. Lookups
(`findIdx?`) and `argTypesAlign` are discharged by small lemma chains, because
derived `DecidableEq` instances are not exposed and the kernel cannot evaluate
`==` on `UF`/`TermType` in a module.

### Coverage

Everything `translateQuery` supports:

- Bool/Int: literals, `not`, `and`, `or`, `implies`, `eq`, `ite`, `<=`, `<`,
  `>=`, `>`, `+`, `-`, `*`, `div`, `mod`, `neg`, `abs`
- uninterpreted functions of any arity, bound variables, `∀`/`∃`
- interpreted functions (`define-fun`)
- uninterpreted sorts, including parameterized ones
- sort synonyms (substituted away, as `denoteQuery` does)
- bitvectors: all operators handled by `translateQuery`
- strings: literals, `str_length`, `str_concat`
- arrays: `select`, `store` (`Map` with `useArrayTheory` on and off)
- options: `none`, `some`

Not handled by either side: datatypes, `option_get`, reals, regexes,
`distinct`, chained comparisons with more than two operands.

## Changes by file

### New: `Strata/DL/SMT/DenoteLemmas.lean`

The lemma library (proved once, with `import all Strata.DL.SMT.Denote`):
per-constructor `den_*` lemmas, closure lemmas for `denoteQuery`,
`denoteBoolTermFromContext` and the `bindIFs`/`bindUFs`/`bindUSs` steps,
quantifier and function-definition builders, and side-condition lemmas.

### `Strata/DL/SMT/Denote.lean`

- `@[expose]` added to 15 definitions:
  - sort level: `denoteFunSort`, `denoteSorts`, `applyTypeArg`,
    `applyTypeArgs`, `mkNonemptyPred`;
  - sort-synonym substitution: `substituteIS`, `substituteISs`,
    `substituteTermVarIS`, `substituteUFIS`, `substituteTermIS`,
    `substituteTermISs`, `substituteTermISss`, `substituteIFIS`,
    `mkISContext`, `mkISContext.go`. The kernel evaluates these only for
    queries that have synonyms.
- The `where` helpers of `denoteBoolTermFromContext` (`bindUSs`, `bindISs`,
  `bindUFs`, `bindIFs`) and `mkISContext.go` became top-level definitions:
  `where` helpers are private in the module system, so lemmas could not name
  them. Their bodies are unchanged.

### `Strata/DL/SMT/TermType.lean`

- `@[expose]` on `TermType.beq` and on the derived `DecidableEq TermPrimType`
  (in an `@[expose] section`). Lookups of a variable or UF must skip entries
  that share its name but not its type or signature; the lemmas
  `findIdx_var_tail_ty` and `findIdx_uf_tail_sig` do that with a
  `TermType.beq … = false` hypothesis, which importers' kernels can now
  evaluate.

### `Strata/DL/SMT/Translate.lean`

- **Fix:** `bvudiv` translated to `/` on `BitVec` (`x / 0 = 0`) instead of
  `BitVec.smtUDiv` (`x / 0` = all ones), disagreeing with the SMT-LIB
  semantics in `denoteTerm`. While `translateQuery` was trusted, goals with
  the wrong semantics could be proved.
- `abs` now uses the `Int.decLt` instance, as `denoteTerm` does (previously
  `Classical.propDecidable`: same meaning, not definitionally equal).
- Added translations of `.none` and `.some`.

### `Strata/MetaVerifier.lean`

- `Strata.SMT.ProofGen`: the proof producer (`proveQuery`). It walks the
  `toExpr` literal of each query in step with its Lean value, instantiates
  lemmas without beta-reducing their arguments (`lemType`), hash-conses the
  term and memoizes per (context, subterm) so repeated subterms yield a
  shared proof DAG.
- Characterization lemmas: `smtVCsCorrect_of`, `denoteQueries_nil/_cons`,
  `denoteQueries_go_nil/_go_cons`, `denoteQuery_toCore_of`.
- `denoteQueries.go` hoisted out of a `where` (same reason as above).
- `substituteSynonyms`: `createGoal` substitutes sort synonyms before calling
  `translateQuery` (its `let` bindings hid synonym definitions from bitvector
  operators).
- The tactic no longer unfolds `smtVCsCorrect` or rewrites the goal.
- `ToExpr (Map α β)` emits a plain list literal instead of the non-exposed
  `Map.ofList`.

### Tests

- New `StrataTest/DL/SMT/DenoteProofTests.lean`: 46 queries covering each
  construct; for each it runs `translateQuery` and `proveQuery` and
  kernel-checks `denoteQuery ctx ts t = some P`. Also checks that a query whose
  translation is not its denotation is rejected.
- `StrataTest/Languages/Core/Examples/GenSMTVCsAxioms.lean`: pins
  `#print axioms` (no bridge axiom) for integer, uninterpreted-sort and
  bitvector programs.
- `Strata.lean` imports the new module.

## Performance

Wall time per file on synthetic programs (includes parsing and VC
generation):

| Workload | `main` (bridge axiom) | old defeq | new |
|---|---|---|---|
| 100 sequential assignments | 1.80 s | 1.99 s | 1.66 s |
| 80 quantified axioms | 3.41 s | 4.30 s | 2.86 s |
| 8 sequential `if`s (VC ≈ 88k term nodes) | 3.27 s | 3.23 s | 2.32 s |
| 10 sequential `if`s (VC ≈ 800k term nodes) | 25.3 s | 20.8 s | 10.9 s |

The `if` VCs grow exponentially because of symbolic evaluation, independently
of this change; after hash-consing, the 800k-node VC has only 313 distinct
subterms. Proof production itself takes about 40 ms there: it reuses the
hash-consed expressions of the VC instead of rebuilding the query body.

Most of the remaining time is Strata code running in the interpreter. At
n = 10, the SMT encoding of the VC (`toSMTVCs`, ≈3.1 s; symbolic execution is
only ≈0.2 s) runs twice, once to obtain the VCs and once in the kernel's
`native_decide` check, plus `translateQuery` (≈1 s) and `toExpr` (≈0.7 s).
Without `native_decide`, the kernel checks the proof in 20 ms. With Strata's
and StrataDDM's native code loaded (`--load-dynlib`), the same file takes
2.6 s instead of 12.4 s. Setting `precompileModules = true` for the `Strata`
library alone does not work, because its native code needs StrataDDM's, which
is not precompiled.

## Possible follow-ups

- Precompile Strata and StrataDDM (`precompileModules`, which needs a change in
  StrataDDM too) so that VC generation and `native_decide` run natively.
- Reduce the exponential growth of the VCs in symbolic execution or the SMT
  encoding (e.g. by naming shared subterms), which would shrink every phase.
- Replace the exposed synonym-substitution functions by lemma chains if fewer
  exposes are preferred (at the cost of a second traversal for queries with
  synonyms).
- Extend `translateQuery` and the lemmas together to further constructs
  (datatypes, `option_get`, `distinct`, n-ary comparisons).
