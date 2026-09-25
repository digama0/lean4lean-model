import Lean4LeanModel.ModelConstruction
import Lean4Lean.Theory.Typing.Lemmas

/-!
# The target theorem

Consistency of Lean's type theory, relative to the existence of `ω` inaccessible cardinals --
the soundness theorem of *The Type Theory of Lean*.

The type theory itself is the one formalized in `Lean4Lean.Theory`: `VExpr` is the term syntax,
`VEnv` the declaration environment, `VEnv.WF` says the environment was built by well-founded
declarations (`VDecl.WF`), and `VEnv.HasType` is the typing judgment.

The final contradiction is proved from semantic soundness. Local declaration-model placeholders are
isolated in `ModelConstructionDebt`; the semantic stack also depends on the explicitly audited
upstream `sorry` theorems described in `Upstream`.
-/

namespace Lean4LeanModel

open Lean4Lean

universe u

/--
**Naive consistency statement.** Assuming `ω` inaccessible cardinals, no well-formed environment
proves `∀ (p : Prop), p` -- in any number `U` of universe parameters, in the empty local context.

This unrestricted statement is refutable: a well-formed environment may declare an axiom of
`VExpr.false`. Its axiom-case `sorry` is therefore a known-false statement placeholder, not an
unfinished proof, while the true statement admitting Lean's standard axioms is being specified.
-/
theorem consistency (hlarge : OmegaInaccessibles.{u}) {env : VEnv} (henv : env.WF) (U : Nat) :
    ¬ ∃ e, env.HasType U [] e VExpr.false := by
  obtain ⟨κ, hκ, hi⟩ := hlarge
  obtain ⟨assignment, M⟩ := model_of_wf hκ hi henv
  rintro ⟨e, he⟩
  let L := List.replicate U 0
  have heL : env.HasType L.length [] e VExpr.false := by
    simpa [L] using he
  have hmem := fundamental_hasType M heL trivial (ModelsCtx.nil (L := L))
  rw [interp_false_eq_empty κ env assignment L] at hmem
  simp at hmem

end Lean4LeanModel
