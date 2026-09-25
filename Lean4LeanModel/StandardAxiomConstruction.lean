import Lean4LeanModel.ModelConstruction
import Lean4LeanModel.StandardAxiomModel

/-!
# Installing the standard axiom meanings

This module isolates the syntactic interpretation equalities needed to turn the semantic values of
the standard three axioms into `AxiomMeaning`s. The interface is independent of the predicate an
upstream environment uses to permit those axioms.
-/

namespace Lean4LeanModel

open Lean4Lean

universe u

/-- Exact generated-type bridges for the standard three declarations. These are deliberately
separate from the canonical semantic invariants established by the inductive and quotient models. -/
structure StandardAxiomTypeBridges (κ : ℕ → Cardinal.{u}) (env : VEnv)
    (assignment : Assignment.{u}) : Prop where
  propext : interp κ env assignment [] [] []
    (StandardAxiom.declaration .propext).type = propextTypeValue assignment
  choice : ∀ n, interp κ env assignment [n] [] []
    (StandardAxiom.declaration .choice).type = choiceTypeValue κ assignment n
  quotSound : ∀ n, interp κ env assignment [n] [] []
    (StandardAxiom.declaration .quotSound).type = quotSoundTypeValue κ assignment n

/-- Canonical semantic meaning for any one of the standard axiom declarations. -/
noncomputable def standardAxiomMeaning {κ : ℕ → Cardinal.{u}} {env : VEnv}
    {assignment : Assignment.{u}} (hi : ∀ n, (κ n).IsInaccessible)
    (hmodels : assignment.ModelsStandardInductives κ)
    (hbridges : StandardAxiomTypeBridges κ env assignment)
    (a : StandardAxiom) : AxiomMeaning κ env assignment a.declaration := by
  cases a with
  | propext =>
      exact {
        value := fun _ => propextConstValue
        valid := by
          intro ns hns
          have : ns = [] := List.length_eq_zero_iff.1 (by simpa using hns)
          subst ns
          rw [hbridges.propext]
          exact propextConstValue_mem hi hmodels.eq hmodels.iff }
  | choice =>
      exact {
        value := fun ns => choiceConstValue κ (ns.getD 0 0)
        valid := by
          intro ns hns
          obtain ⟨n, rfl⟩ := List.length_eq_one_iff.1 (by simpa using hns)
          rw [hbridges.choice]
          exact choiceConstValue_mem hmodels.nonempty n }
  | quotSound =>
      exact {
        value := fun _ => quotSoundConstValue
        valid := by
          intro ns hns
          obtain ⟨n, rfl⟩ := List.length_eq_one_iff.1 (by simpa using hns)
          rw [hbridges.quotSound]
          exact quotSoundConstValue_mem hi hmodels.eq n }

/-- Predicate-agnostic adapter: once a proposed allowed-axiom predicate has been reduced to the
standard declaration enum, the corresponding semantic meaning is immediate. -/
noncomputable def standardAxiomMeaningOfAllowed {κ : ℕ → Cardinal.{u}} {env : VEnv}
    {assignment : Assignment.{u}} {P : VConstVal → Prop}
    (hi : ∀ n, (κ n).IsInaccessible)
    (hmodels : assignment.ModelsStandardInductives κ)
    (hbridges : StandardAxiomTypeBridges κ env assignment)
    (toStandard : ∀ ci, P ci → ∃ a : StandardAxiom,
      ci = StandardAxiom.declaration a)
    {ci : VConstVal} (hci : P ci) : AxiomMeaning κ env assignment ci := by
  classical
  let a := Classical.choose (toStandard ci hci)
  have ha : ci = StandardAxiom.declaration a := Classical.choose_spec (toStandard ci hci)
  exact ha.symm ▸ standardAxiomMeaning hi hmodels hbridges a

end Lean4LeanModel
