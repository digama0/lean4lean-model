import Lean4LeanModel.QuotientModel
import Lean4LeanModel.StandardAxioms

/-!
# Semantic meanings of the standard axioms

This module states the canonical `Iff` and `Nonempty` invariants alongside `ModelsEq`, then
constructs the proof/data values needed by `propext`, `Classical.choice`, and `Quot.sound`.
The constructions are independent of how the corresponding inductive declarations are eventually
installed by lean4lean.
-/

namespace Lean4LeanModel

open Lean4Lean

universe u

noncomputable def assignedIffValue (assignment : Assignment.{u}) (P Q : ZFSet.{u}) : ZFSet.{u} :=
  depApp (depApp (assignment.constVal ``Iff []) P) Q

def Assignment.ModelsIff (assignment : Assignment.{u}) : Prop :=
  ∀ P ∈ (propUniverse : ZFSet.{u}), ∀ Q ∈ (propUniverse : ZFSet.{u}),
    assignedIffValue assignment P Q = truthValue (bullet ∈ P ↔ bullet ∈ Q)

theorem Assignment.ModelsIff.congr {assignment assignment' : Assignment.{u}}
    (hIff : assignment.ModelsIff)
    (h : assignment'.constVal ``Iff [] = assignment.constVal ``Iff []) :
    assignment'.ModelsIff := by
  intro P hP Q hQ
  simpa [assignedIffValue, h] using hIff P hP Q hQ

noncomputable def assignedNonemptyValue (assignment : Assignment.{u}) (n : Nat)
    (A : ZFSet.{u}) : ZFSet.{u} :=
  depApp (assignment.constVal ``Nonempty [n]) A

def Assignment.ModelsNonempty (κ : ℕ → Cardinal.{u}) (assignment : Assignment.{u}) : Prop :=
  ∀ n, ∀ A ∈ ModelUniverse κ n,
    assignedNonemptyValue assignment n A = truthValue (∃ a, a ∈ A)

theorem Assignment.ModelsNonempty.congr {κ : ℕ → Cardinal.{u}}
    {assignment assignment' : Assignment.{u}} (hNonempty : assignment.ModelsNonempty κ)
    (h : ∀ n, assignment'.constVal ``Nonempty [n] = assignment.constVal ``Nonempty [n]) :
    assignment'.ModelsNonempty κ := by
  intro n A hA
  simpa [assignedNonemptyValue, h n] using hNonempty n A hA

/-- Canonical meanings of the three inductive type formers used by Lean's standard axioms. -/
structure Assignment.ModelsStandardInductives (κ : ℕ → Cardinal.{u})
    (assignment : Assignment.{u}) : Prop where
  eq : assignment.ModelsEq κ
  iff : assignment.ModelsIff
  nonempty : assignment.ModelsNonempty κ

theorem Assignment.ModelsStandardInductives.congr {κ : ℕ → Cardinal.{u}}
    {assignment assignment' : Assignment.{u}}
    (h : assignment.ModelsStandardInductives κ)
    (hEq : ∀ ns, assignment'.constVal ``Eq ns = assignment.constVal ``Eq ns)
    (hIff : assignment'.constVal ``Iff [] = assignment.constVal ``Iff [])
    (hNonempty : ∀ n,
      assignment'.constVal ``Nonempty [n] = assignment.constVal ``Nonempty [n]) :
    assignment'.ModelsStandardInductives κ :=
  ⟨h.eq.congr hEq, h.iff.congr hIff, h.nonempty.congr hNonempty⟩

/-- Semantic type of `propext` under assigned `Iff` and `Eq` interpretations. -/
noncomputable def propextTypeValue (assignment : Assignment.{u}) : ZFSet.{u} :=
  forallValue propUniverse fun P =>
    forallValue propUniverse fun Q =>
      forallValue (assignedIffValue assignment P Q) fun _ =>
        assignedEqValue assignment 1 propUniverse P Q

noncomputable def propextConstValue : ZFSet.{u} := bullet

private theorem prop_eq_of_iff {P Q : ZFSet.{u}}
    (hP : P ∈ (propUniverse : ZFSet.{u})) (hQ : Q ∈ (propUniverse : ZFSet.{u}))
    (h : bullet ∈ P ↔ bullet ∈ Q) : P = Q := by
  rcases eq_empty_or_singleton_of_mem_propUniverse hP with rfl | rfl <;>
    rcases eq_empty_or_singleton_of_mem_propUniverse hQ with rfl | rfl <;> simp_all

theorem propextConstValue_mem {κ : ℕ → Cardinal.{u}} {assignment : Assignment.{u}}
    (hi : ∀ n, (κ n).IsInaccessible)
    (hEq : assignment.ModelsEq κ) (hIff : assignment.ModelsIff) :
    propextConstValue ∈ propextTypeValue assignment := by
  simp only [propextConstValue, propextTypeValue, bullet_mem_forallValue]
  intro P hP Q hQ h hiff
  rw [hIff P hP Q hQ, mem_truthValue] at hiff
  have hProp : (propUniverse : ZFSet.{u}) ∈ ModelUniverse κ 1 := by
    simpa using propUniverse_mem_vonNeumann (hi 0)
  rw [hEq 1 propUniverse hProp P hP Q hQ, bullet_mem_truthValue]
  exact prop_eq_of_iff hP hQ hiff.1

/-- Choose an element from a nonempty semantic type; the default is unreachable in typed uses. -/
noncomputable def choiceElement (A : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if h : ∃ a, a ∈ A then Classical.choose h else ∅

theorem choiceElement_mem {A : ZFSet.{u}} (h : ∃ a, a ∈ A) : choiceElement A ∈ A := by
  classical
  simp only [choiceElement, dif_pos h]
  exact Classical.choose_spec h

noncomputable def choiceTypeValue (κ : ℕ → Cardinal.{u})
    (assignment : Assignment.{u}) (n : Nat) : ZFSet.{u} :=
  piValue n (ModelUniverse κ n) fun A =>
    piValue n (assignedNonemptyValue assignment n A) fun _ => A

noncomputable def choiceConstValue (κ : ℕ → Cardinal.{u}) (n : Nat) : ZFSet.{u} :=
  lamValue n (ModelUniverse κ n) fun A =>
    lamValue n (truthValue (∃ a, a ∈ A)) fun _ => choiceElement A

theorem choiceConstValue_mem {κ : ℕ → Cardinal.{u}} {assignment : Assignment.{u}}
    (hNonempty : assignment.ModelsNonempty κ) (n : Nat) :
    choiceConstValue κ n ∈ choiceTypeValue κ assignment n := by
  unfold choiceConstValue choiceTypeValue
  apply lamValue_mem_piValue
  · intro A hA
    rw [hNonempty n A hA]
    apply lamValue_mem_piValue
    · intro _ h
      exact choiceElement_mem (mem_truthValue.1 h).1
    · intro hn _ _
      subst n
      simpa using hA
  · intro hn A hA
    subst n
    exact forallValue_mem_propUniverse _ _

/-- Semantic type of `Quot.sound` after its implicit parameters are exposed. -/
noncomputable def quotSoundTypeValue (κ : ℕ → Cardinal.{u})
    (assignment : Assignment.{u}) (n : Nat) : ZFSet.{u} :=
  forallValue (ModelUniverse κ n) fun A =>
    forallValue (relationSpace A) fun r =>
      forallValue A fun a =>
        forallValue A fun b =>
          forallValue (depApp (depApp r a) b) fun _ =>
            assignedEqValue assignment n (quotValue n A (relationOfGraph r))
              (quotMkValue n A (relationOfGraph r) a)
              (quotMkValue n A (relationOfGraph r) b)

noncomputable def quotSoundConstValue : ZFSet.{u} := bullet

theorem quotSoundConstValue_mem {κ : ℕ → Cardinal.{u}} {assignment : Assignment.{u}}
    (hi : ∀ n, (κ n).IsInaccessible) (hEq : assignment.ModelsEq κ) (n : Nat) :
    quotSoundConstValue ∈ quotSoundTypeValue κ assignment n := by
  simp only [quotSoundConstValue, quotSoundTypeValue, bullet_mem_forallValue]
  intro A hA r hr a ha b hb h hab
  have hrab : depApp (depApp r a) b ∈ (propUniverse : ZFSet.{u}) :=
    relationOfGraph_mem_prop hr ha hb
  have hh : h = bullet := eq_bullet_of_mem_prop hrab hab
  subst h
  exact quotSound_semantic hi hEq hA ha hb hab

end Lean4LeanModel
