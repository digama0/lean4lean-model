import Lean4LeanModel.AxiomEnv
import Lean4Lean.Theory.Typing.Lemmas
import Mathlib.SetTheory.Cardinal.Regular

/-!
# The target theorems

Consistency of Lean's type theory, relative to the existence of `ω` inaccessible cardinals --
the soundness theorem of *The Type Theory of Lean*.

The type theory is the one formalized in `Lean4Lean.Theory`: `VExpr` is the term syntax, `VEnv`
the declaration environment, `VEnv.WF` says the environment was built by well-formed declarations,
and `VEnv.HasType` is the typing judgment.

The statement is split so that the axioms are handled once and separately from everything else:

* `consistent_of_extendsAxioms` -- an environment that assumes nothing beyond a base environment
  is consistent whenever that base is. This is where definitions, quotients and inductives are
  discharged, and it is independent of which axioms the base declares.
* `consistent_empty` -- the axiom-free case, i.e. the base is `VEnv.empty`.
* `consistent_leanAxiomEnv` -- Lean's own base: `propext`, `Quot.sound`, `Classical.choice`.
  This is the step that needs the inaccessibles.

`exists_inconsistent_wf_environment` below is why the split is necessary rather than convenient.
-/

namespace Lean4LeanModel

open Lean4Lean Cardinal

universe u

/--
`∀ (α : Sort 0), α`, i.e. `∀ (p : Prop), p`.

This is the environment-independent stand-in for `False`: a `VEnv` need not contain the `False`
inductive at all, and any proof of `False` in an environment that does yields a proof of this.
-/
def VExpr.false : VExpr := .forallE (.sort .zero) (.bvar 0)

/-- An environment is consistent when it proves no closed instance of `∀ (p : Prop), p`, in any
number `U` of universe parameters. -/
def Consistent (env : VEnv) : Prop := ∀ U e, ¬ env.HasType U [] e VExpr.false

/-! ## Why the axioms must be isolated -/

private def falseAxiom : VConstVal where
  name := `Lean4LeanModel.falseAxiom
  uvars := 0
  type := VExpr.false

/--
Well-formedness alone never implies consistency: an environment may declare `∀ (p : Prop), p` as
an axiom. So consistency can only ever be stated relative to what an environment is allowed to
assume, which is what `ExtendsAxioms` pins down.

(From https://github.com/digama0/lean4lean-model/pull/1.)
-/
theorem exists_inconsistent_wf_environment :
    ∃ env : VEnv, env.WF ∧ ¬ Consistent env := by
  have hfalse : VConstant.WF .empty falseAxiom.toVConstant :=
    ⟨.imax (.succ .zero) .zero, .forallEDF (.sortDF (by trivial) (by trivial) rfl) (.bvar .zero)⟩
  have hadd : ∃ env, VEnv.empty.addConst falseAxiom.name falseAxiom.toVConstant = some env := by
    simp [VEnv.addConst, VEnv.empty]
  obtain ⟨env, hadd⟩ := hadd
  refine ⟨env, ⟨[.axiom falseAxiom], .decl (.axiom hfalse hadd) .empty⟩, fun H => ?_⟩
  exact H 0 (.const falseAxiom.name []) <|
    .constDF (VEnv.addConst_self hadd) (by simp) (by simp) (by simp [falseAxiom]) .nil

/-! ## Conservativity over a base -/

/--
**Assuming nothing new preserves consistency.** If `env` is well-formed, keeps `base`'s constants
and definitional equalities, and declares no axiom that `base` does not already declare, then
`env` is consistent as soon as `base` is.

Everything that is not an axiom is discharged here: `def`, `opaque` and `example` carry a value,
`quot` adds the quotient constants and their computation rule, and `induct` is constrained by
`VInductDecl.WF`. The inductive case is blocked upstream, where `VInductDecl.WF` and
`VEnv.addInduct` are still `sorry` and so supply nothing to build an interpretation from.
-/
theorem consistent_of_extendsAxioms {base env : VEnv}
    (_ : Consistent base) (_ : ExtendsAxioms base env) : Consistent env := by
  sorry

/-! ## The two bases -/

/--
**The axiom-free base.** `VEnv.empty` proves nothing, so by `consistent_of_extendsAxioms` no
axiom-free environment does either.
-/
theorem consistent_empty : Consistent .empty := by
  sorry

/--
There are `ω` inaccessible cardinals: a strictly increasing `ℕ`-indexed sequence of them, one to
interpret each Lean universe `Sort 0, Sort 1, ...`.

Lean itself cannot prove this: its foundations give only `v`-many inaccessibles in universe `v`
(`Cardinal.IsInaccessible.univ`), i.e. a numeral's worth for any fixed universe, never `ω` of
them in a single `Cardinal.{u}`. That gap is exactly the consistency strength the theorem below
assumes, and is why this is a hypothesis rather than a lemma.
-/
def OmegaInaccessibles : Prop :=
  ∃ κ : ℕ → Cardinal.{u}, StrictMono κ ∧ ∀ n, (κ n).IsInaccessible

/--
**Lean's base is consistent.** Assuming `ω` inaccessible cardinals, `propext`, `Quot.sound` and
`Classical.choice` -- over the constants that give their types meaning -- prove no falsehood.

This is where the model is built: `Sort n` is interpreted by the `n`-th inaccessible, `Prop`
proof-irrelevantly and two-valued (which validates `propext`), `Quot` by quotients (which
validates `Quot.sound`), and `Classical.choice` by choice in the metatheory.
-/
theorem consistent_leanAxiomEnv (_ : OmegaInaccessibles.{u}) : Consistent leanAxiomEnv := by
  sorry

/--
**Consistency of Lean.** An environment whose axioms are Lean's three, and which otherwise only
defines things, proves no falsehood.
-/
theorem consistency (h : OmegaInaccessibles.{u}) {env : VEnv}
    (hext : ExtendsAxioms leanAxiomEnv env) : Consistent env :=
  consistent_of_extendsAxioms (consistent_leanAxiomEnv h) hext

end Lean4LeanModel
