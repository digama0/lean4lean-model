import Lean4Lean.Theory.Meta
import Lean4Lean.Theory.VDecl

/-!
# The standard axioms as declarations

This module identifies the three axiom declarations supported by Lean's standard metatheory. It
does not prescribe how an environment should express that no other axioms occur: clients only need
to map their chosen condition to `AxiomsSatisfy IsStandardAxiom`.
-/

namespace Lean4LeanModel

open Lean4Lean

/-- The three axioms admitted by Lean's standard metatheory. -/
inductive StandardAxiom where
  | propext
  | choice
  | quotSound
  deriving DecidableEq, Repr

namespace StandardAxiom

/-- The exact name and kernel-elaborated type of a standard axiom declaration. These are pinned by
the repository's Lean version. `Quot.sound` is forward-looking: pinned lean4lean's `addQuot` does
not itself add that declaration. -/
def declaration : StandardAxiom → VConstVal
  | .propext => { name := ``propext, toVConstant := vconst(type_of% @propext) }
  | .choice => { name := ``Classical.choice, toVConstant := vconst(type_of% @Classical.choice) }
  | .quotSound => { name := ``Quot.sound, toVConstant := vconst(type_of% @Quot.sound) }

@[simp] theorem declaration_name :
    (declaration a).name = match a with
      | .propext => ``propext
      | .choice => ``Classical.choice
      | .quotSound => ``Quot.sound := by
  cases a <;> rfl

@[simp] theorem declaration_uvars :
    (declaration a).uvars = match a with
      | .propext => 0
      | .choice => 1
      | .quotSound => 1 := by
  cases a <;> rfl

end StandardAxiom

/-- A declaration is one of the exact standard three, including both its name and type. -/
def IsStandardAxiom (ci : VConstVal) : Prop :=
  ∃ a : StandardAxiom, ci = a.declaration

/-- Every axiom declaration occurring in `ds` satisfies `P`. This deliberately says nothing about
the representation of an allowed-environment predicate; it is the small history-level adapter
target consumed by the semantic construction. An environment-level upstream policy can remain in
its native form and prove a bridge to this predicate once for its chosen `VEnv.WF'` witness. -/
def AxiomsSatisfy (P : VConstVal → Prop) (ds : List VDecl) : Prop :=
  ∀ ci, .axiom ci ∈ ds → P ci

namespace AxiomsSatisfy

theorem nil (P : VConstVal → Prop) : AxiomsSatisfy P [] := by
  intro ci h
  simp at h

theorem tail {P : VConstVal → Prop} {d : VDecl} {ds : List VDecl}
    (h : AxiomsSatisfy P (d :: ds)) : AxiomsSatisfy P ds := by
  intro ci hci
  exact h ci (List.mem_cons_of_mem d hci)

theorem head {P : VConstVal → Prop} {ci : VConstVal} {ds : List VDecl}
    (h : AxiomsSatisfy P (.axiom ci :: ds)) : P ci :=
  h ci (by simp)

theorem mono {P Q : VConstVal → Prop} {ds : List VDecl}
    (hpq : ∀ ci, P ci → Q ci) (h : AxiomsSatisfy P ds) : AxiomsSatisfy Q ds := by
  intro ci hci
  exact hpq ci (h ci hci)

end AxiomsSatisfy

end Lean4LeanModel
