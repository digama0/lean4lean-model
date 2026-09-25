import Lean4LeanModel.Grothendieck
import Lean4Lean.Theory.VLevel
import Mathlib.Data.List.GetD

/-!
# Universes for the set-theoretic model

The proof-irrelevant universe is the powerset of a singleton. Positive universes are stages of
the von Neumann hierarchy indexed by a strictly increasing sequence of inaccessible cardinals.
-/

namespace Lean4LeanModel

open Lean4Lean Cardinal Order

universe u

/-- The unique semantic value of every proof. -/
noncomputable def bullet : ZFSet.{u} := ∅

/-- The set-theoretic truth value of a metatheoretic proposition. -/
noncomputable def truthValue (p : Prop) : ZFSet.{u} :=
  ZFSet.sep (fun _ => p) {bullet}

/-- The proof-irrelevant universe of propositions. -/
noncomputable def propUniverse : ZFSet.{u} :=
  ZFSet.powerset {bullet}

/-- The semantic universe hierarchy associated to `κ`. -/
noncomputable def ModelUniverse (κ : ℕ → Cardinal.{u}) : ℕ → ZFSet.{u}
  | 0 => propUniverse
  | n + 1 => ZFSet.vonNeumann (κ n).ord

/-- Interpret a syntactic universe level under a valuation of its parameters. -/
noncomputable def interpLevel (κ : ℕ → Cardinal.{u}) (L : List Nat) (l : VLevel) : ZFSet.{u} :=
  ModelUniverse κ (l.eval L)

@[simp]
theorem mem_truthValue {p : Prop} {x : ZFSet.{u}} :
    x ∈ truthValue p ↔ p ∧ x = bullet := by
  by_cases h : p <;> simp [truthValue, h]

theorem truthValue_of_pos (p : Prop) (h : p) : truthValue p = ({bullet} : ZFSet.{u}) := by
  apply ZFSet.ext
  simp [truthValue, h]

theorem truthValue_of_neg (p : Prop) (h : ¬p) : truthValue p = (∅ : ZFSet.{u}) := by
  apply ZFSet.ext
  simp [truthValue, h]

@[simp]
theorem bullet_mem_truthValue {p : Prop} :
    (bullet : ZFSet.{u}) ∈ truthValue p ↔ p := by
  simp

@[simp]
theorem mem_propUniverse {x : ZFSet.{u}} :
    x ∈ propUniverse ↔ x ⊆ {bullet} := by
  simp [propUniverse]

theorem eq_bullet_of_mem_prop {p x : ZFSet.{u}}
    (hp : p ∈ propUniverse) (hx : x ∈ p) : x = bullet :=
  ZFSet.mem_singleton.1 (mem_propUniverse.1 hp hx)

theorem eq_empty_or_singleton_of_mem_propUniverse {x : ZFSet.{u}}
    (hx : x ∈ propUniverse) : x = ∅ ∨ x = {bullet} := by
  by_cases hb : bullet ∈ x
  · right
    apply ZFSet.ext
    intro y
    constructor
    · intro hy
      exact ZFSet.mem_singleton.2 (eq_bullet_of_mem_prop hx hy)
    · intro hy
      rw [ZFSet.mem_singleton] at hy
      simpa [hy] using hb
  · left
    rw [ZFSet.eq_empty]
    intro y hy
    exact hb ((eq_bullet_of_mem_prop hx hy) ▸ hy)

@[simp]
theorem empty_mem_propUniverse : (∅ : ZFSet.{u}) ∈ propUniverse := by
  rw [mem_propUniverse]
  exact ZFSet.empty_subset _

@[simp]
theorem singleton_bullet_mem_propUniverse : ({bullet} : ZFSet.{u}) ∈ propUniverse := by
  rw [mem_propUniverse]

theorem propUniverse_eq_pair :
    (propUniverse : ZFSet.{u}) = {∅, {bullet}} := by
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    exact ZFSet.mem_pair.2 (eq_empty_or_singleton_of_mem_propUniverse hx)
  · intro hx
    rcases ZFSet.mem_pair.1 hx with rfl | rfl <;> simp

theorem isTransitive_propUniverse : ZFSet.IsTransitive (propUniverse : ZFSet.{u}) := by
  intro x hx y hy
  rw [eq_bullet_of_mem_prop hx hy]
  simp [bullet]

theorem truthValue_mem_propUniverse (p : Prop) :
    truthValue p ∈ (propUniverse : ZFSet.{u}) := by
  rw [mem_propUniverse]
  intro x hx
  exact ZFSet.mem_singleton.2 (mem_truthValue.1 hx).2

@[simp]
theorem ModelUniverse_zero (κ : ℕ → Cardinal.{u}) :
    ModelUniverse κ 0 = propUniverse := rfl

@[simp]
theorem ModelUniverse_succ (κ : ℕ → Cardinal.{u}) (n : Nat) :
    ModelUniverse κ (n + 1) = ZFSet.vonNeumann (κ n).ord := rfl

theorem propUniverse_mem_vonNeumann {c : Cardinal.{u}} (hc : c.IsInaccessible) :
    propUniverse ∈ ZFSet.vonNeumann c.ord := by
  exact smallAt_powerset hc (smallAt_singleton hc (smallAt_empty hc))

theorem smallAt_iff_mem_ModelUniverse {κ : ℕ → Cardinal.{u}} {n : Nat} {x : ZFSet.{u}} :
    SmallAt (κ n) x ↔ x ∈ ModelUniverse κ (n + 1) :=
  Iff.rfl

theorem ModelUniverse_mem_succ {κ : ℕ → Cardinal.{u}}
    (hκ : StrictMono κ) (hi : ∀ n, (κ n).IsInaccessible) (n : Nat) :
    ModelUniverse κ n ∈ ModelUniverse κ (n + 1) := by
  cases n with
  | zero =>
      simpa using propUniverse_mem_vonNeumann (hi 0)
  | succ n =>
      exact ZFSet.vonNeumann_mem_of_lt (Cardinal.ord_strictMono (hκ (Nat.lt_succ_self n)))

theorem ModelUniverse_subset_succ {κ : ℕ → Cardinal.{u}}
    (hκ : StrictMono κ) (hi : ∀ n, (κ n).IsInaccessible) (n : Nat) :
    ModelUniverse κ n ⊆ ModelUniverse κ (n + 1) := by
  intro x hx
  exact ZFSet.isTransitive_vonNeumann _ _ (ModelUniverse_mem_succ hκ hi n) hx

theorem ModelUniverse_mono {κ : ℕ → Cardinal.{u}}
    (hκ : StrictMono κ) (hi : ∀ n, (κ n).IsInaccessible) {m n : Nat} (h : m ≤ n) :
    ModelUniverse κ m ⊆ ModelUniverse κ n := by
  induction h with
  | refl => exact fun _ => id
  | @step n h ih => exact fun _ hx => ModelUniverse_subset_succ hκ hi n (ih hx)

theorem ModelUniverse_mem_of_lt {κ : ℕ → Cardinal.{u}}
    (hκ : StrictMono κ) (hi : ∀ n, (κ n).IsInaccessible) {m n : Nat} (h : m < n) :
    ModelUniverse κ m ∈ ModelUniverse κ n :=
  ModelUniverse_mono hκ hi (Nat.succ_le_iff.2 h) (ModelUniverse_mem_succ hκ hi m)

theorem isTransitive_ModelUniverse (κ : ℕ → Cardinal.{u}) (n : Nat) :
    ZFSet.IsTransitive (ModelUniverse κ n) := by
  cases n with
  | zero => exact isTransitive_propUniverse
  | succ n => exact ZFSet.isTransitive_vonNeumann _

theorem interpLevel_equiv {κ : ℕ → Cardinal.{u}} {L : List Nat} {l l' : VLevel}
    (h : l ≈ l') : interpLevel κ L l = interpLevel κ L l' := by
  exact congrArg (ModelUniverse κ) (VLevel.equiv_def.1 h L)

theorem interpLevel_mono {κ : ℕ → Cardinal.{u}}
    (hκ : StrictMono κ) (hi : ∀ n, (κ n).IsInaccessible)
    {L : List Nat} {l l' : VLevel} (h : l ≤ l') :
    interpLevel κ L l ⊆ interpLevel κ L l' :=
  ModelUniverse_mono hκ hi (h L)

@[simp]
theorem interpLevel_inst (κ : ℕ → Cardinal.{u}) (ns : List Nat)
    (ls : List VLevel) (l : VLevel) :
    interpLevel κ ns (l.inst ls) = interpLevel κ (ls.map (VLevel.eval ns)) l := by
  simp [interpLevel, VLevel.eval_inst]

theorem interpLevel_append (κ : ℕ → Cardinal.{u}) (ns ms : List Nat)
    (l : VLevel) (hl : l.WF ns.length) :
    interpLevel κ (ns ++ ms) l = interpLevel κ ns l := by
  apply congrArg (ModelUniverse κ)
  induction l with
  | zero => rfl
  | succ l ih => simpa [VLevel.WF, VLevel.eval] using congrArg Nat.succ (ih hl)
  | max l₁ l₂ ih₁ ih₂ =>
      exact congrArg₂ Nat.max (ih₁ hl.1) (ih₂ hl.2)
  | imax l₁ l₂ ih₁ ih₂ =>
      exact congrArg₂ Nat.imax (ih₁ hl.1) (ih₂ hl.2)
  | param i =>
      simpa [VLevel.eval] using List.getD_append ns ms 0 i hl

section SanityChecks

variable {κ : ℕ → Cardinal.{u}}

example : interpLevel κ [] .zero = propUniverse := rfl

example : interpLevel κ [] (.succ .zero) = ZFSet.vonNeumann (κ 0).ord := rfl

example (hκ : StrictMono κ) (hi : ∀ n, (κ n).IsInaccessible) :
    interpLevel κ [] .zero ∈ interpLevel κ [] (.succ .zero) :=
  ModelUniverse_mem_succ hκ hi 0

example (ns : List Nat) :
    interpLevel κ ns (.succ (.param 0)) = ModelUniverse κ (ns.getD 0 0 + 1) := rfl

end SanityChecks

end Lean4LeanModel
