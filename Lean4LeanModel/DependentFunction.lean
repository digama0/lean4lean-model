import Lean4LeanModel.Universe

/-!
# Set-theoretic dependent functions

Dependent functions are represented by Kuratowski graphs. The constructions in this file are
the semantic operations used for type-valued products, abstraction, and application.
-/

namespace Lean4LeanModel

open Cardinal

universe u

/-- The set of pairs whose first component lies in `A` and whose second lies in the corresponding
fiber `B a`. -/
noncomputable def depRelation (A : ZFSet.{u}) (B : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  boundedUnion (fun a => repl (ZFSet.pair a) (B a)) A

@[simp]
theorem mem_depRelation {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}} {z : ZFSet.{u}} :
    z ∈ depRelation A B ↔ ∃ a ∈ A, ∃ b ∈ B a, ZFSet.pair a b = z := by
  simp [depRelation]

/-- A graph is a dependent function when it has exactly one output in each fiber. -/
def IsDepFunc (A : ZFSet.{u}) (B : ZFSet.{u} → ZFSet.{u}) (f : ZFSet.{u}) : Prop :=
  f ⊆ depRelation A B ∧ ∀ a ∈ A, ∃! b, ZFSet.pair a b ∈ f

/-- Functionality of a graph over `A`, independent of the codomain family used to type it. -/
def IsFuncGraph (A f : ZFSet.{u}) : Prop :=
  (∀ z ∈ f, ∃ a ∈ A, ∃ b, ZFSet.pair a b = z) ∧
    ∀ a ∈ A, ∃! b, ZFSet.pair a b ∈ f

/-- The set of all dependent functions from `A` into `B`. -/
noncomputable def depFuns (A : ZFSet.{u}) (B : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (IsDepFunc A B) (ZFSet.powerset (depRelation A B))

@[simp]
theorem mem_depFuns {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}} {f : ZFSet.{u}} :
    f ∈ depFuns A B ↔ IsDepFunc A B f := by
  simp [depFuns, IsDepFunc]

/-- Graph abstraction over a set-sized domain. -/
noncomputable def depLam (A : ZFSet.{u}) (f : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  repl (fun a => ZFSet.pair a (f a)) A

@[simp]
theorem mem_depLam {A : ZFSet.{u}} {f : ZFSet.{u} → ZFSet.{u}} {z : ZFSet.{u}} :
    z ∈ depLam A f ↔ ∃ a ∈ A, ZFSet.pair a (f a) = z := by
  simp [depLam]

@[simp]
theorem pair_mem_depLam {A : ZFSet.{u}} {f : ZFSet.{u} → ZFSet.{u}} {a b : ZFSet.{u}} :
    ZFSet.pair a b ∈ depLam A f ↔ a ∈ A ∧ f a = b := by
  constructor
  · intro h
    obtain ⟨a', ha', hp⟩ := mem_depLam.1 h
    have hp' := ZFSet.pair_injective hp
    rcases hp' with ⟨rfl, hp'⟩
    exact ⟨ha', hp'⟩
  · rintro ⟨ha, rfl⟩
    exact mem_depLam.2 ⟨a, ha, rfl⟩

theorem depLam_isDepFunc {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    {f : ZFSet.{u} → ZFSet.{u}} (hf : ∀ a ∈ A, f a ∈ B a) :
    IsDepFunc A B (depLam A f) := by
  constructor
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := mem_depLam.1 hz
    exact mem_depRelation.2 ⟨a, ha, f a, hf a ha, rfl⟩
  · intro a ha
    refine ⟨f a, pair_mem_depLam.2 ⟨ha, rfl⟩, ?_⟩
    intro b hb
    exact (pair_mem_depLam.1 hb).2.symm

theorem depLam_isFuncGraph {A : ZFSet.{u}} {f : ZFSet.{u} → ZFSet.{u}} :
    IsFuncGraph A (depLam A f) := by
  constructor
  · intro z hz
    obtain ⟨a, ha, heq⟩ := mem_depLam.1 hz
    exact ⟨a, ha, f a, heq⟩
  · intro a ha
    refine ⟨f a, pair_mem_depLam.2 ⟨ha, rfl⟩, ?_⟩
    intro b hb
    exact (pair_mem_depLam.1 hb).2.symm

theorem depLam_mem_depFuns {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    {f : ZFSet.{u} → ZFSet.{u}} (hf : ∀ a ∈ A, f a ∈ B a) :
    depLam A f ∈ depFuns A B :=
  mem_depFuns.2 (depLam_isDepFunc hf)

/-- Application of a functional graph, with `∅` as the unreachable malformed-graph default. -/
noncomputable def depApp (f a : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if h : ∃! b, ZFSet.pair a b ∈ f then Classical.choose h else ∅

theorem depApp_eq_of_pair {f a b : ZFSet.{u}}
    (hu : ∃! b, ZFSet.pair a b ∈ f) (hb : ZFSet.pair a b ∈ f) : depApp f a = b := by
  classical
  simp only [depApp, dif_pos hu]
  exact ((Classical.choose_spec hu).2 b hb).symm

theorem pair_depApp_mem_of_unique {f a : ZFSet.{u}}
    (hu : ∃! b, ZFSet.pair a b ∈ f) : ZFSet.pair a (depApp f a) ∈ f := by
  classical
  simp only [depApp, dif_pos hu]
  exact (Classical.choose_spec hu).1

theorem pair_depApp_mem {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    {f a : ZFSet.{u}} (hf : IsDepFunc A B f) (ha : a ∈ A) :
    ZFSet.pair a (depApp f a) ∈ f := by
  exact pair_depApp_mem_of_unique (hf.2 a ha)

theorem pair_depApp_mem_of_funcGraph {A f a : ZFSet.{u}}
    (hf : IsFuncGraph A f) (ha : a ∈ A) : ZFSet.pair a (depApp f a) ∈ f :=
  pair_depApp_mem_of_unique (hf.2 a ha)

theorem depApp_mem {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    {f a : ZFSet.{u}} (hf : IsDepFunc A B f) (ha : a ∈ A) : depApp f a ∈ B a := by
  have hp := hf.1 (pair_depApp_mem hf ha)
  obtain ⟨a', _, b, hb, heq⟩ := mem_depRelation.1 hp
  have hab := ZFSet.pair_injective heq
  rcases hab with ⟨rfl, rfl⟩
  exact hb

@[simp]
theorem depApp_depLam {A : ZFSet.{u}} {f : ZFSet.{u} → ZFSet.{u}}
    {a : ZFSet.{u}} (ha : a ∈ A) : depApp (depLam A f) a = f a := by
  apply depApp_eq_of_pair
  · refine ⟨f a, pair_mem_depLam.2 ⟨ha, rfl⟩, ?_⟩
    intro b hb
    exact (pair_mem_depLam.1 hb).2.symm
  · exact pair_mem_depLam.2 ⟨ha, rfl⟩

theorem depLam_depApp {A f : ZFSet.{u}} (hf : IsFuncGraph A f) : depLam A (depApp f) = f := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨a, ha, rfl⟩ := mem_depLam.1 hz
    exact pair_depApp_mem_of_funcGraph hf ha
  · intro hz
    obtain ⟨a, ha, b, rfl⟩ := hf.1 _ hz
    rw [pair_mem_depLam]
    refine ⟨ha, ?_⟩
    exact depApp_eq_of_pair (hf.2 a ha) hz

theorem IsDepFunc.isFuncGraph {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}} {f : ZFSet.{u}}
    (hf : IsDepFunc A B f) : IsFuncGraph A f := by
  refine ⟨?_, hf.2⟩
  intro z hz
  obtain ⟨a, ha, b, _, heq⟩ := mem_depRelation.1 (hf.1 hz)
  exact ⟨a, ha, b, heq⟩

theorem depLam_depApp_of_mem {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    {f : ZFSet.{u}} (hf : f ∈ depFuns A B) : depLam A (depApp f) = f :=
  depLam_depApp (mem_depFuns.1 hf).isFuncGraph

theorem IsFuncGraph.ext {A f g : ZFSet.{u}} (hf : IsFuncGraph A f) (hg : IsFuncGraph A g)
    (h : ∀ a ∈ A, depApp f a = depApp g a) : f = g := by
  rw [← depLam_depApp hf, ← depLam_depApp hg]
  apply ZFSet.ext
  intro z
  simp only [mem_depLam]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, congrArg (ZFSet.pair a) (h a ha).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, congrArg (ZFSet.pair a) (h a ha)⟩

theorem depRelation_congr {A : ZFSet.{u}} {B B' : ZFSet.{u} → ZFSet.{u}}
    (h : ∀ a ∈ A, B a = B' a) : depRelation A B = depRelation A B' := by
  apply ZFSet.ext
  intro z
  simp only [mem_depRelation]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, (h a ha) ▸ hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, b, (h a ha).symm ▸ hb, rfl⟩

theorem depFuns_congr {A : ZFSet.{u}} {B B' : ZFSet.{u} → ZFSet.{u}}
    (h : ∀ a ∈ A, B a = B' a) : depFuns A B = depFuns A B' := by
  have hr := depRelation_congr h
  apply ZFSet.ext
  intro f
  simp only [mem_depFuns, IsDepFunc]
  rw [hr]

theorem depLam_congr {A : ZFSet.{u}} {f f' : ZFSet.{u} → ZFSet.{u}}
    (h : ∀ a ∈ A, f a = f' a) : depLam A f = depLam A f' := by
  apply ZFSet.ext
  intro z
  simp only [mem_depLam]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, congrArg (ZFSet.pair a) (h a ha).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, congrArg (ZFSet.pair a) (h a ha)⟩

/-- Logical universal quantification, used when the codomain of a `forallE` is `Prop`. -/
noncomputable def forallValue (A : ZFSet.{u}) (B : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  truthValue (∀ a ∈ A, bullet ∈ B a)

@[simp]
theorem bullet_mem_forallValue {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}} :
    bullet ∈ forallValue A B ↔ ∀ a ∈ A, bullet ∈ B a := by
  simp [forallValue]

theorem forallValue_mem_propUniverse (A : ZFSet.{u}) (B : ZFSet.{u} → ZFSet.{u}) :
    forallValue A B ∈ (propUniverse : ZFSet.{u}) :=
  truthValue_mem_propUniverse _

theorem forallValue_congr {A : ZFSet.{u}} {B B' : ZFSet.{u} → ZFSet.{u}}
    (h : ∀ a ∈ A, B a = B' a) : forallValue A B = forallValue A B' := by
  apply congrArg truthValue
  apply propext
  constructor
  · intro hB a ha
    exact (h a ha) ▸ hB a ha
  · intro hB a ha
    exact (h a ha).symm ▸ hB a ha

/-- Semantic dependent product, dispatched by the evaluated codomain universe. -/
noncomputable def piValue (n : Nat) (A : ZFSet.{u})
    (B : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  if n = 0 then forallValue A B else depFuns A B

/-- Semantic abstraction, dispatched by the evaluated codomain universe. -/
noncomputable def lamValue (n : Nat) (A : ZFSet.{u})
    (f : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  if n = 0 then bullet else depLam A f

/-- Semantic application, dispatched by the evaluated codomain universe. -/
noncomputable def appValue (n : Nat) (f a : ZFSet.{u}) : ZFSet.{u} :=
  if n = 0 then bullet else depApp f a

/-- Dispatch depends only on whether the supplied class is zero. -/
theorem piValue_congr_zero {n m : Nat} (h : (n = 0 ↔ m = 0))
    (A : ZFSet.{u}) (B : ZFSet.{u} → ZFSet.{u}) :
    piValue n A B = piValue m A B := by
  by_cases hn : n = 0
  · simp [piValue, hn, h.1 hn]
  · have hm : m ≠ 0 := fun hm => hn (h.2 hm)
    simp [piValue, hn, hm]

/-- Dispatch depends only on whether the supplied class is zero. -/
theorem lamValue_congr_zero {n m : Nat} (h : (n = 0 ↔ m = 0))
    (A : ZFSet.{u}) (f : ZFSet.{u} → ZFSet.{u}) :
    lamValue n A f = lamValue m A f := by
  by_cases hn : n = 0
  · simp [lamValue, hn, h.1 hn]
  · have hm : m ≠ 0 := fun hm => hn (h.2 hm)
    simp [lamValue, hn, hm]

/-- Dispatch depends only on whether the supplied class is zero. -/
theorem appValue_congr_zero {n m : Nat} (h : (n = 0 ↔ m = 0))
    (f a : ZFSet.{u}) : appValue n f a = appValue m f a := by
  by_cases hn : n = 0
  · simp [appValue, hn, h.1 hn]
  · have hm : m ≠ 0 := fun hm => hn (h.2 hm)
    simp [appValue, hn, hm]

theorem piValue_congr {n : Nat} {A : ZFSet.{u}} {B B' : ZFSet.{u} → ZFSet.{u}}
    (h : ∀ a ∈ A, B a = B' a) : piValue n A B = piValue n A B' := by
  by_cases hn : n = 0
  · simpa [piValue, hn] using forallValue_congr h
  · simpa [piValue, hn] using depFuns_congr h

theorem lamValue_congr {n : Nat} {A : ZFSet.{u}} {f f' : ZFSet.{u} → ZFSet.{u}}
    (h : ∀ a ∈ A, f a = f' a) : lamValue n A f = lamValue n A f' := by
  by_cases hn : n = 0
  · simp [lamValue, hn]
  · simpa [lamValue, hn] using depLam_congr h

theorem lamValue_mem_piValue {n : Nat} {A : ZFSet.{u}}
    {B f : ZFSet.{u} → ZFSet.{u}}
    (hf : ∀ a ∈ A, f a ∈ B a)
    (hB : n = 0 → ∀ a ∈ A, B a ∈ (propUniverse : ZFSet.{u})) :
    lamValue n A f ∈ piValue n A B := by
  by_cases hn : n = 0
  · simp only [lamValue, piValue, if_pos hn, bullet_mem_forallValue]
    intro a ha
    have hfa := hf a ha
    simpa [eq_bullet_of_mem_prop (hB hn a ha) hfa] using hfa
  · simp only [lamValue, piValue, if_neg hn]
    exact depLam_mem_depFuns hf

theorem appValue_mem {n : Nat} {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    {f a : ZFSet.{u}} (hf : f ∈ piValue n A B) (ha : a ∈ A) : appValue n f a ∈ B a := by
  by_cases hn : n = 0
  · simp only [appValue, if_pos hn]
    have hforall : bullet ∈ forallValue A B := by
      have hproof : f = bullet :=
        eq_bullet_of_mem_prop (forallValue_mem_propUniverse A B) (by simpa [piValue, hn] using hf)
      simpa [hproof, piValue, hn] using hf
    exact bullet_mem_forallValue.1 hforall a ha
  · simp only [appValue, if_neg hn]
    exact depApp_mem (mem_depFuns.1 (by simpa [piValue, hn] using hf)) ha

theorem appValue_lamValue {n : Nat} {A : ZFSet.{u}}
    {B f : ZFSet.{u} → ZFSet.{u}} {a : ZFSet.{u}}
    (hf : ∀ a ∈ A, f a ∈ B a)
    (hB : n = 0 → ∀ a ∈ A, B a ∈ (propUniverse : ZFSet.{u})) (ha : a ∈ A) :
    appValue n (lamValue n A f) a = f a := by
  by_cases hn : n = 0
  · simp only [appValue, lamValue, if_pos hn]
    exact (eq_bullet_of_mem_prop (hB hn a ha) (hf a ha)).symm
  · simp only [appValue, lamValue, if_neg hn]
    exact depApp_depLam ha

theorem lamValue_appValue {n : Nat} {A : ZFSet.{u}}
    {B : ZFSet.{u} → ZFSet.{u}} {f : ZFSet.{u}} (hf : f ∈ piValue n A B) :
    lamValue n A (appValue n f) = f := by
  by_cases hn : n = 0
  · simp only [lamValue, if_pos hn]
    exact (eq_bullet_of_mem_prop (forallValue_mem_propUniverse A B)
      (by simpa [piValue, hn] using hf)).symm
  · simp only [lamValue, if_neg hn]
    have happ : appValue n f = depApp f := by
      funext a
      simp [appValue, hn]
    rw [happ]
    have hmem : f ∈ depFuns A B := by simpa [piValue, hn] using hf
    have hdep : IsDepFunc A B f := mem_depFuns.1 hmem
    have hgraph : IsFuncGraph A f := IsDepFunc.isFuncGraph (B := B) hdep
    exact depLam_depApp (A := A) (f := f) hgraph

theorem smallAt_depRelation {c : Cardinal.{u}} (hc : c.IsInaccessible)
    {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (hA : SmallAt c A) (hB : ∀ a ∈ A, SmallAt c (B a)) : SmallAt c (depRelation A B) := by
  apply smallAt_boundedUnion hc hA
  intro a ha
  apply smallAt_repl hc (hB a ha)
  intro b hb
  exact smallAt_orderedPair hc (smallAt_mem ha hA) (smallAt_mem hb (hB a ha))

theorem smallAt_depFuns {c : Cardinal.{u}} (hc : c.IsInaccessible)
    {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (hA : SmallAt c A) (hB : ∀ a ∈ A, SmallAt c (B a)) : SmallAt c (depFuns A B) := by
  exact smallAt_of_subset ZFSet.sep_subset (smallAt_powerset hc (smallAt_depRelation hc hA hB))

theorem smallAt_depLam {c : Cardinal.{u}} (hc : c.IsInaccessible)
    {A : ZFSet.{u}} {f : ZFSet.{u} → ZFSet.{u}}
    (hA : SmallAt c A) (hf : ∀ a ∈ A, SmallAt c (f a)) : SmallAt c (depLam A f) :=
  smallAt_graph hc hA hf

theorem smallAt_depApp {c : Cardinal.{u}} {A : ZFSet.{u}}
    {B : ZFSet.{u} → ZFSet.{u}} {f a : ZFSet.{u}}
    (hf : IsDepFunc A B f) (ha : a ∈ A) (hB : SmallAt c (B a)) : SmallAt c (depApp f a) :=
  smallAt_mem (depApp_mem hf ha) hB

theorem depFuns_mem_ModelUniverse {κ : ℕ → Cardinal.{u}}
    (hκ : StrictMono κ) (hi : ∀ n, (κ n).IsInaccessible)
    {m n : Nat} {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (hA : A ∈ ModelUniverse κ m) (hB : ∀ a ∈ A, B a ∈ ModelUniverse κ (n + 1)) :
    depFuns A B ∈ ModelUniverse κ (Nat.max m (n + 1)) := by
  let r := Nat.max m (n + 1)
  change depFuns A B ∈ ModelUniverse κ r
  have hr : 0 < r := (Nat.zero_lt_succ n).trans_le (Nat.le_max_right m (n + 1))
  have hA' : A ∈ ModelUniverse κ r := ModelUniverse_mono hκ hi (Nat.le_max_left _ _) hA
  have hB' : ∀ a ∈ A, B a ∈ ModelUniverse κ r := fun a ha =>
    ModelUniverse_mono hκ hi (Nat.le_max_right _ _) (hB a ha)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  rw [hk] at hA' hB' ⊢
  change SmallAt (κ k) A at hA'
  change ∀ a ∈ A, SmallAt (κ k) (B a) at hB'
  change SmallAt (κ k) (depFuns A B)
  exact smallAt_depFuns (hi k) hA' hB'

theorem piValue_mem_ModelUniverse {κ : ℕ → Cardinal.{u}}
    (hκ : StrictMono κ) (hi : ∀ n, (κ n).IsInaccessible)
    {m n : Nat} {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (hA : A ∈ ModelUniverse κ m) (hB : ∀ a ∈ A, B a ∈ ModelUniverse κ n) :
    piValue n A B ∈ ModelUniverse κ (Nat.imax m n) := by
  cases n with
  | zero => simpa [piValue, Nat.imax] using forallValue_mem_propUniverse A B
  | succ n => simpa [piValue, Nat.imax] using depFuns_mem_ModelUniverse hκ hi hA hB

/-- Universe closure with a dispatcher represented independently from the true universe index. -/
theorem piValue_mem_ModelUniverse_of_zero_iff {κ : ℕ → Cardinal.{u}}
    (hκ : StrictMono κ) (hi : ∀ n, (κ n).IsInaccessible)
    {k m n : Nat} {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (hk : k = 0 ↔ n = 0)
    (hA : A ∈ ModelUniverse κ m) (hB : ∀ a ∈ A, B a ∈ ModelUniverse κ n) :
    piValue k A B ∈ ModelUniverse κ (Nat.imax m n) := by
  rw [piValue_congr_zero hk A B]
  exact piValue_mem_ModelUniverse hκ hi hA hB

section SanityChecks

variable (A : ZFSet.{u}) (B f : ZFSet.{u} → ZFSet.{u})

example : piValue 0 A B = forallValue A B := by simp [piValue]

example (n : Nat) : piValue (n + 1) A B = depFuns A B := by simp [piValue]

example : lamValue 0 A f = bullet := by simp [lamValue]

example (n : Nat) : lamValue (n + 1) A f = depLam A f := by simp [lamValue]

end SanityChecks

end Lean4LeanModel
