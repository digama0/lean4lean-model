import Lean4LeanModel.Grothendieck
import Mathlib.Logic.Relation

/-!
# Set-sized quotients

This module constructs the quotient of a `ZFSet` by an arbitrary metatheoretic relation. Lean's
`Quot` does not require the relation to be an equivalence relation, so classes are taken with
respect to `Relation.EqvGen`. Quotient elements are represented by their equivalence classes as
subsets of the original set.
-/

namespace Lean4LeanModel

universe u

/-- Restrict a metatheoretic relation to elements of `A`. -/
def SetQuotRel (A : ZFSet.{u}) (R : ZFSet.{u} → ZFSet.{u} → Prop) (a b : ZFSet.{u}) : Prop :=
  a ∈ A ∧ b ∈ A ∧ R a b

/-- Equivalence closure of a relation restricted to `A`. -/
abbrev SetQuotEqv (A : ZFSet.{u}) (R : ZFSet.{u} → ZFSet.{u} → Prop) :=
  Relation.EqvGen (SetQuotRel A R)

/-- The equivalence class of `a`, represented as a subset of `A`. -/
noncomputable def setQuotClass (A : ZFSet.{u})
    (R : ZFSet.{u} → ZFSet.{u} → Prop) (a : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun b => SetQuotEqv A R a b) A

@[simp]
theorem mem_setQuotClass {A : ZFSet.{u}} {R : ZFSet.{u} → ZFSet.{u} → Prop}
    {a b : ZFSet.{u}} :
    b ∈ setQuotClass A R a ↔ b ∈ A ∧ SetQuotEqv A R a b := by
  simp [setQuotClass]

theorem setQuotClass_subset (A : ZFSet.{u}) (R : ZFSet.{u} → ZFSet.{u} → Prop)
    (a : ZFSet.{u}) : setQuotClass A R a ⊆ A :=
  ZFSet.sep_subset

theorem self_mem_setQuotClass {A : ZFSet.{u}} {R : ZFSet.{u} → ZFSet.{u} → Prop}
    {a : ZFSet.{u}} (ha : a ∈ A) : a ∈ setQuotClass A R a :=
  mem_setQuotClass.2 ⟨ha, .refl _⟩

theorem setQuotEqv_of_rel {A : ZFSet.{u}} {R : ZFSet.{u} → ZFSet.{u} → Prop}
    {a b : ZFSet.{u}} (ha : a ∈ A) (hb : b ∈ A) (hab : R a b) :
    SetQuotEqv A R a b :=
  .rel _ _ ⟨ha, hb, hab⟩

theorem setQuotClass_eq_of_eqv {A : ZFSet.{u}} {R : ZFSet.{u} → ZFSet.{u} → Prop}
    {a b : ZFSet.{u}} (hab : SetQuotEqv A R a b) :
    setQuotClass A R a = setQuotClass A R b := by
  apply ZFSet.ext
  intro x
  simp only [mem_setQuotClass]
  constructor
  · rintro ⟨hx, hax⟩
    exact ⟨hx, .trans _ a _ (.symm _ _ hab) hax⟩
  · rintro ⟨hx, hbx⟩
    exact ⟨hx, .trans _ b _ hab hbx⟩

theorem setQuotClass_eq_iff {A : ZFSet.{u}} {R : ZFSet.{u} → ZFSet.{u} → Prop}
    {a b : ZFSet.{u}} (hb : b ∈ A) :
    setQuotClass A R a = setQuotClass A R b ↔ SetQuotEqv A R a b := by
  constructor
  · intro h
    have : b ∈ setQuotClass A R a := h ▸ self_mem_setQuotClass hb
    exact (mem_setQuotClass.1 this).2
  · exact setQuotClass_eq_of_eqv

/-- The set of equivalence classes of elements of `A`. -/
noncomputable def setQuotient (A : ZFSet.{u})
    (R : ZFSet.{u} → ZFSet.{u} → Prop) : ZFSet.{u} :=
  repl (setQuotClass A R) A

@[simp]
theorem mem_setQuotient {A : ZFSet.{u}} {R : ZFSet.{u} → ZFSet.{u} → Prop}
    {q : ZFSet.{u}} :
    q ∈ setQuotient A R ↔ ∃ a ∈ A, setQuotClass A R a = q := by
  simp [setQuotient]

theorem setQuotClass_mem_setQuotient {A : ZFSet.{u}}
    {R : ZFSet.{u} → ZFSet.{u} → Prop} {a : ZFSet.{u}} (ha : a ∈ A) :
    setQuotClass A R a ∈ setQuotient A R :=
  mem_setQuotient.2 ⟨a, ha, rfl⟩

/-- Related elements have equal images in the set quotient. -/
theorem setQuot_sound {A : ZFSet.{u}} {R : ZFSet.{u} → ZFSet.{u} → Prop}
    {a b : ZFSet.{u}} (ha : a ∈ A) (hb : b ∈ A) (hab : R a b) :
    setQuotClass A R a = setQuotClass A R b :=
  setQuotClass_eq_of_eqv (setQuotEqv_of_rel ha hb hab)

/-- A function respecting `R` respects its equivalence closure. -/
theorem eq_of_setQuotEqv {A : ZFSet.{u}} {R : ZFSet.{u} → ZFSet.{u} → Prop}
    {f : ZFSet.{u} → ZFSet.{u}}
    (hf : ∀ a ∈ A, ∀ b ∈ A, R a b → f a = f b)
    {a b : ZFSet.{u}} (hab : SetQuotEqv A R a b) : f a = f b := by
  induction hab with
  | rel a b h => exact hf a h.1 b h.2.1 h.2.2
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Evaluation of a relation-respecting function on a quotient class. The default is unreachable
for members of `setQuotient`. -/
noncomputable def setQuotLift (A : ZFSet.{u})
    (R : ZFSet.{u} → ZFSet.{u} → Prop) (f : ZFSet.{u} → ZFSet.{u})
    (q : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if h : ∃ a ∈ A, setQuotClass A R a = q then f (Classical.choose h) else ∅

theorem setQuotLift_class {A : ZFSet.{u}} {R : ZFSet.{u} → ZFSet.{u} → Prop}
    {f : ZFSet.{u} → ZFSet.{u}}
    (hf : ∀ a ∈ A, ∀ b ∈ A, R a b → f a = f b)
    {a : ZFSet.{u}} (ha : a ∈ A) :
    setQuotLift A R f (setQuotClass A R a) = f a := by
  classical
  have hrep : ∃ b ∈ A, setQuotClass A R b = setQuotClass A R a := ⟨a, ha, rfl⟩
  simp only [setQuotLift, dif_pos hrep]
  have hchosen := (Classical.choose_spec hrep).2
  exact eq_of_setQuotEqv hf ((setQuotClass_eq_iff ha).1 hchosen)

theorem setQuotLift_mem {A : ZFSet.{u}} {R : ZFSet.{u} → ZFSet.{u} → Prop}
    {f : ZFSet.{u} → ZFSet.{u}}
    (hf : ∀ a ∈ A, ∀ b ∈ A, R a b → f a = f b)
    {B q : ZFSet.{u}} (hfB : ∀ a ∈ A, f a ∈ B) (hq : q ∈ setQuotient A R) :
    setQuotLift A R f q ∈ B := by
  obtain ⟨a, ha, rfl⟩ := mem_setQuotient.1 hq
  rw [setQuotLift_class hf ha]
  exact hfB a ha

/-- Every element of a set quotient has a representative. This is the semantic content needed for
`Quot.ind`. -/
theorem setQuot_ind {A : ZFSet.{u}} {R : ZFSet.{u} → ZFSet.{u} → Prop}
    {P : ZFSet.{u} → Prop} (hP : ∀ a ∈ A, P (setQuotClass A R a))
    {q : ZFSet.{u}} (hq : q ∈ setQuotient A R) : P q := by
  obtain ⟨a, ha, rfl⟩ := mem_setQuotient.1 hq
  exact hP a ha

theorem smallAt_setQuotClass {c : Cardinal.{u}} {A : ZFSet.{u}}
    {R : ZFSet.{u} → ZFSet.{u} → Prop} (hA : SmallAt c A) (a : ZFSet.{u}) :
    SmallAt c (setQuotClass A R a) :=
  smallAt_of_subset (setQuotClass_subset A R a) hA

theorem smallAt_setQuotient {c : Cardinal.{u}} (hc : c.IsInaccessible)
    {A : ZFSet.{u}} {R : ZFSet.{u} → ZFSet.{u} → Prop} (hA : SmallAt c A) :
    SmallAt c (setQuotient A R) := by
  apply smallAt_repl hc hA
  intro a _
  exact smallAt_setQuotClass hA a

theorem smallAt_setQuotLift {c : Cardinal.{u}} {A : ZFSet.{u}}
    {R : ZFSet.{u} → ZFSet.{u} → Prop} {f : ZFSet.{u} → ZFSet.{u}}
    (hf : ∀ a ∈ A, ∀ b ∈ A, R a b → f a = f b)
    {q : ZFSet.{u}} (hq : q ∈ setQuotient A R)
    (hsmall : ∀ a ∈ A, SmallAt c (f a)) : SmallAt c (setQuotLift A R f q) := by
  obtain ⟨a, ha, rfl⟩ := mem_setQuotient.1 hq
  rw [setQuotLift_class hf ha]
  exact hsmall a ha

end Lean4LeanModel
