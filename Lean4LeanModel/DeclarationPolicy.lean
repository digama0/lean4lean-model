import Lean4Lean.Theory.Typing.Env

/-!
# Declaration policies

`Lean4Lean.VEnv.WF` permits arbitrary well-typed axioms -- including `∀ (p : Prop), p` -- so
consistency is never a consequence of well-formedness alone. What an environment may assume is
therefore isolated into a *base environment*, and the remaining declarations are constrained by a
policy saying that they introduce nothing new to assume.

The `WFUnder` machinery is from https://github.com/digama0/lean4lean-model/pull/1.
-/

namespace Lean4LeanModel

open Lean4Lean

/-- A well-formed environment with a declaration history accepted by `allowed`. -/
def WFUnder (allowed : VDecl → Prop) (env : VEnv) : Prop :=
  ∃ ds, VEnv.WF' ds env ∧ ∀ d ∈ ds, allowed d

/-- Forgetting the declaration policy leaves an ordinary well-formed environment. -/
theorem WFUnder.wf {allowed : VDecl → Prop} {env : VEnv} :
    WFUnder allowed env → VEnv.WF env
  | ⟨ds, hds, _⟩ => ⟨ds, hds⟩

/-- Extend a policy-compliant history by one policy-compliant declaration. -/
theorem WFUnder.decl {allowed : VDecl → Prop} {env env' : VEnv} {d : VDecl}
    (h : WFUnder allowed env) (hd : VDecl.WF env d env') (ha : allowed d) :
    WFUnder allowed env' := by
  obtain ⟨ds, hds, hall⟩ := h
  refine ⟨d :: ds, .decl hd hds, ?_⟩
  intro d' hd'
  simp only [List.mem_cons] at hd'
  rcases hd' with rfl | hd'
  · exact ha
  · exact hall d' hd'

/-- Weakening a declaration policy preserves well-formedness under that policy. -/
theorem WFUnder.mono {allowed allowed' : VDecl → Prop} {env : VEnv}
    (h : WFUnder allowed env) (hle : ∀ d, allowed d → allowed' d) :
    WFUnder allowed' env := by
  obtain ⟨ds, hds, hall⟩ := h
  exact ⟨ds, hds, fun d hd => hle d (hall d hd)⟩

/--
Which declarations a history may contain, parameterized by which axioms are permitted.

The match is deliberately exhaustive: a new declaration form upstream must be reviewed before it
enters the modeled fragment. Everything other than `axiom` is allowed, since no other form lets an
environment assume anything: `def`, `opaque` and `example` require a value, `quot` adds the
quotient constants and computation rule (`Quot.sound` is a separate axiom), and `induct` is
constrained by `VInductDecl.WF`.
-/
def DeclPolicy (axioms : VConstVal → Prop) : VDecl → Prop
  | .block _ => True
  | .axiom ci => axioms ci
  | .def _ => True
  | .opaque _ => True
  | .example _ => True
  | .quot => True
  | .induct _ => True

/--
The `#print axioms`-style check: every axiom in the history is one that `base` already declares,
with the same type. Since `VEnv.addConst` rejects a name the environment already has, this says
exactly that the history introduces *no* axiom of its own.
-/
def NoNewAxioms (base : VEnv) : VDecl → Prop :=
  DeclPolicy fun ci => base.constants ci.name = some ci.toVConstant

/--
`env` assumes nothing beyond `base`: it is well-formed, its axioms are `base`'s axioms, and it
retains `base`'s constants and definitional equalities.

This is decidable in the declaration history, which is what makes it an effective check on a real
environment: walk the history and confirm each `axiom` against the `base` table.
-/
structure ExtendsAxioms (base env : VEnv) : Prop where
  /-- The history introduces no axiom that `base` does not already declare. -/
  noNewAxioms : WFUnder (NoNewAxioms base) env
  /-- `env` keeps the constants and definitional equalities of `base`. -/
  le : base ≤ env

theorem ExtendsAxioms.wf {base env : VEnv} (h : ExtendsAxioms base env) : VEnv.WF env :=
  h.noNewAxioms.wf

/-- Over the empty base, `NoNewAxioms` forbids axioms outright. -/
theorem noNewAxioms_empty_iff {d : VDecl} :
    NoNewAxioms .empty d ↔ DeclPolicy (fun _ => False) d := by
  cases d <;> simp [NoNewAxioms, DeclPolicy, VEnv.empty]

end Lean4LeanModel
