import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Typing.Lemmas

/-!
# Extending an environment

`Lean4Lean.VEnv.WF` permits arbitrary well-typed axioms -- including `∀ (p : Prop), p` -- so
consistency is never a consequence of well-formedness alone. What an environment may assume is
therefore isolated into a *base environment*, and everything else is built on top of it by
declarations that assume nothing: every `VDecl.WF` constructor except `axiom`.

Building *from* the base, rather than checking a history that starts from `VEnv.empty`, is what
makes the base's meanings stick. The base already declares `Eq`, `Nonempty` and friends, so
`VEnv.addConst` rejects any later declaration of those names, and no definition can install a
same-typed impostor. Pinning the constants alone would not be enough: `Nonempty α` is a `Prop`, so
with `proofIrrel` and `Classical.choice` in scope, a definition `Nonempty := fun _ => ⊤` admits
`fun h t => h (Classical.choice t)` as its own `Nonempty.rec`, and then `Classical.choice` inhabits
every type.

The counterexample below and the idea of constraining the declaration history are from
https://github.com/digama0/lean4lean-model/pull/1.
-/

namespace Lean4LeanModel

open Lean4Lean

/--
Which declarations may extend the base, parameterized by which axioms are permitted.

The match is deliberately exhaustive: a new declaration form upstream must be reviewed before it
enters the modeled fragment.
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
Every declaration form except `axiom`.

`def`, `opaque` and `example` require a value, `quot` adds the quotient constants and their
computation rule (`Quot.sound` is an axiom and so lives in the base), and `induct` is constrained
by `VInductDecl.WF`. None of them lets an environment assume anything new.
-/
def NoAxioms : VDecl → Prop := DeclPolicy fun _ => False

/-- `env` is reachable from `base` by declarations satisfying `allowed`. -/
inductive ExtendsBy (allowed : VDecl → Prop) (base : VEnv) : VEnv → Prop where
  | refl : ExtendsBy allowed base base
  | decl {env env' : VEnv} {d : VDecl} : ExtendsBy allowed base env →
      VDecl.WF env d env' → allowed d → ExtendsBy allowed base env'

/-- `env` assumes nothing beyond `base`: it is reachable from `base` without declaring an axiom. -/
abbrev NoNewAxioms (base env : VEnv) : Prop := ExtendsBy NoAxioms base env

/--
The relation the consistency theorems use: `env` adds no axioms to *some* sub-environment of
`base`.

Weaker than `NoNewAxioms base env`, and weak enough on purpose. Soundness is monotonic in the
trivial direction -- a model of `base` restricts to a model of any `base' ≤ base`, since there is
less to interpret and less to validate -- so a model of `base` still yields one of `env`. This
covers an environment that never declares some of the base's constants, which `NoNewAxioms` would
reject through its `≤` component.
-/
def ExtendsAxioms (base env : VEnv) : Prop := ∃ base', base' ≤ base ∧ NoNewAxioms base' env

namespace ExtendsBy
variable {allowed allowed' : VDecl → Prop} {base env : VEnv}

/-- Extending is transitive, so a base may be reached in stages. -/
theorem trans {a b c : VEnv} (h₁ : ExtendsBy allowed a b) (h₂ : ExtendsBy allowed b c) :
    ExtendsBy allowed a c := by
  induction h₂ with
  | refl => exact h₁
  | decl _ hd ha ih => exact .decl ih hd ha

/-- Weakening the policy preserves reachability. -/
theorem mono (h : ExtendsBy allowed base env) (hle : ∀ d, allowed d → allowed' d) :
    ExtendsBy allowed' base env := by
  induction h with
  | refl => exact .refl
  | decl _ hd ha ih => exact .decl ih hd (hle _ ha)

/-- Everything reachable from `VEnv.empty` is well-formed. -/
theorem wf (h : ExtendsBy allowed .empty env) : VEnv.WF env := by
  induction h with
  | refl => exact ⟨[], .empty⟩
  | decl _ hd _ ih => exact let ⟨ds, hds⟩ := ih; ⟨_ :: ds, .decl hd hds⟩

end ExtendsBy

/--
Adding no axioms retains everything the base had.

This is why `NoNewAxioms` is worth stating on its own: it carries `≤` with it, so the weakened
`ExtendsAxioms` is a genuine weakening rather than an incomparable condition.
-/
theorem NoNewAxioms.le {base env : VEnv} (h : NoNewAxioms base env) : base ≤ env := by
  induction h with
  | refl => exact .rfl
  | @decl env env' d _ hd ha ih =>
    refine VEnv.LE.trans ih ?_
    cases hd with
    | «axiom» => exact absurd ha (by simp [NoAxioms, DeclPolicy])
    | «def» _ h => exact VEnv.LE.trans (VEnv.addConst_le h) VEnv.addDefEq_le
    | «opaque» _ h => exact VEnv.addConst_le h
    | «example» _ => exact .rfl
    | quot _ h =>
      unfold VEnv.addQuot at h
      cases h1 : env.addConst ``Quot quotConst with
      | none => simp [h1] at h
      | some env1 =>
      cases h2 : env1.addConst ``Quot.mk quotMkConst with
      | none => simp [h1, h2] at h
      | some env2 =>
      cases h3 : env2.addConst ``Quot.lift quotLiftConst with
      | none => simp [h1, h2, h3] at h
      | some env3 =>
      cases h4 : env3.addConst ``Quot.ind quotIndConst with
      | none => simp [h1, h2, h3, h4] at h
      | some env4 =>
        simp [h1, h2, h3, h4] at h
        subst h
        exact VEnv.LE.trans (VEnv.addConst_le h1) <| VEnv.LE.trans (VEnv.addConst_le h2) <|
          VEnv.LE.trans (VEnv.addConst_le h3) <|
            VEnv.LE.trans (VEnv.addConst_le h4) VEnv.addDefEq_le
    | induct _ h =>
      -- blocked upstream: `VEnv.addInduct` is `sorry`, so nothing can be said about the
      -- environment it produces.
      sorry

/-- `NoNewAxioms` is the case `base' = base` of `ExtendsAxioms`. -/
theorem NoNewAxioms.extendsAxioms {base env : VEnv} (h : NoNewAxioms base env) :
    ExtendsAxioms base env := ⟨base, .rfl, h⟩

end Lean4LeanModel
