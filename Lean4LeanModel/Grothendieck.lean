import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.Cardinal
import Mathlib.SetTheory.ZFC.VonNeumann

/-!
# Inaccessible stages of the von Neumann hierarchy

This file packages the closure properties of `V_ κ.ord` used by the semantic universes.
-/

namespace Lean4LeanModel

open Cardinal Order

universe u

/--
There are `ω` inaccessible cardinals: a strictly increasing `ℕ`-indexed sequence of them.

Lean itself cannot prove this: its foundations give only `v`-many inaccessibles in universe `v`
(`Cardinal.IsInaccessible.univ`), i.e. a numeral's worth for any fixed universe, never `ω` of
them in a single `Cardinal.{u}`. That gap is exactly the consistency strength assumed by the
model's headline theorem.
-/
def OmegaInaccessibles : Prop :=
  ∃ κ : ℕ → Cardinal.{u}, StrictMono κ ∧ ∀ n, (κ n).IsInaccessible

/-- The initial ordinal of an inaccessible cardinal is a limit ordinal. -/
theorem _root_.Cardinal.IsInaccessible.ord_isSuccLimit {c : Cardinal.{u}} (hc : c.IsInaccessible) :
    IsSuccLimit c.ord :=
  isSuccLimit_ord hc.aleph0_lt.le

/-- Membership in the von Neumann stage associated to a cardinal. -/
def SmallAt (c : Cardinal.{u}) (x : ZFSet.{u}) : Prop :=
  x ∈ ZFSet.vonNeumann c.ord

theorem smallAt_iff_rank_lt {c : Cardinal.{u}} {x : ZFSet.{u}} :
    SmallAt c x ↔ ZFSet.rank x < c.ord :=
  ZFSet.mem_vonNeumann

theorem card_lt_of_smallAt {c : Cardinal.{u}} (hc : c.IsInaccessible)
    {x : ZFSet.{u}} (hx : SmallAt c x) : ZFSet.card x < c := by
  calc
    ZFSet.card x ≤ ZFSet.card (ZFSet.vonNeumann (ZFSet.rank x)) :=
      ZFSet.card_mono (ZFSet.subset_vonNeumann_self x)
    _ = preBeth (ZFSet.rank x) := ZFSet.card_vonNeumann _
    _ < preBeth c.ord := preBeth_strictMono (smallAt_iff_rank_lt.1 hx)
    _ = c := hc.preBeth_ord

theorem smallAt_of_subset {c : Cardinal.{u}} {x y : ZFSet.{u}}
    (hxy : x ⊆ y) (hy : SmallAt c y) : SmallAt c x :=
  ZFSet.mem_vonNeumann_of_subset hxy hy

theorem smallAt_mem {c : Cardinal.{u}} {x y : ZFSet.{u}}
    (hxy : x ∈ y) (hy : SmallAt c y) : SmallAt c x :=
  ZFSet.isTransitive_vonNeumann _ _ hy hxy

theorem smallAt_empty {c : Cardinal.{u}} (hc : c.IsInaccessible) :
    SmallAt c (∅ : ZFSet.{u}) := by
  rw [smallAt_iff_rank_lt, ZFSet.rank_empty]
  exact hc.isRegular.ord_pos

theorem smallAt_singleton {c : Cardinal.{u}} (hc : c.IsInaccessible)
    {x : ZFSet.{u}} (hx : SmallAt c x) : SmallAt c {x} := by
  rw [smallAt_iff_rank_lt, ZFSet.rank_singleton]
  exact hc.ord_isSuccLimit.succ_lt (smallAt_iff_rank_lt.1 hx)

theorem smallAt_insert {c : Cardinal.{u}} (hc : c.IsInaccessible)
    {x y : ZFSet.{u}} (hx : SmallAt c x) (hy : SmallAt c y) : SmallAt c (insert x y) := by
  rw [smallAt_iff_rank_lt, ZFSet.rank_insert]
  exact max_lt
    (hc.ord_isSuccLimit.succ_lt (smallAt_iff_rank_lt.1 hx))
    (smallAt_iff_rank_lt.1 hy)

theorem smallAt_pair {c : Cardinal.{u}} (hc : c.IsInaccessible)
    {x y : ZFSet.{u}} (hx : SmallAt c x) (hy : SmallAt c y) : SmallAt c {x, y} := by
  exact smallAt_insert hc hx (smallAt_singleton hc hy)

theorem smallAt_union {c : Cardinal.{u}} {x y : ZFSet.{u}}
    (hx : SmallAt c x) (hy : SmallAt c y) : SmallAt c (x ∪ y) := by
  rw [smallAt_iff_rank_lt, ZFSet.rank_union]
  exact max_lt (smallAt_iff_rank_lt.1 hx) (smallAt_iff_rank_lt.1 hy)

theorem smallAt_sUnion {c : Cardinal.{u}} {x : ZFSet.{u}}
    (hx : SmallAt c x) : SmallAt c (ZFSet.sUnion x) := by
  rw [smallAt_iff_rank_lt]
  exact (ZFSet.rank_sUnion_le x).trans_lt (smallAt_iff_rank_lt.1 hx)

theorem smallAt_powerset {c : Cardinal.{u}} (hc : c.IsInaccessible)
    {x : ZFSet.{u}} (hx : SmallAt c x) : SmallAt c (ZFSet.powerset x) := by
  rw [smallAt_iff_rank_lt, ZFSet.rank_powerset]
  exact hc.ord_isSuccLimit.succ_lt (smallAt_iff_rank_lt.1 hx)

theorem smallAt_orderedPair {c : Cardinal.{u}} (hc : c.IsInaccessible)
    {x y : ZFSet.{u}} (hx : SmallAt c x) (hy : SmallAt c y) :
    SmallAt c (ZFSet.pair x y) := by
  exact smallAt_pair hc (smallAt_singleton hc hx) (smallAt_pair hc hx hy)

theorem smallAt_prod {c : Cardinal.{u}} (hc : c.IsInaccessible)
    {x y : ZFSet.{u}} (hx : SmallAt c x) (hy : SmallAt c y) :
    SmallAt c (ZFSet.prod x y) := by
  apply smallAt_of_subset (y := ZFSet.powerset (ZFSet.powerset (x ∪ y)))
  · intro z hz
    rw [ZFSet.mem_prod] at hz
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    rw [ZFSet.mem_powerset]
    intro q hq
    rw [ZFSet.mem_powerset]
    intro t ht
    simp only [ZFSet.pair, ZFSet.mem_pair] at hq
    rcases hq with rfl | rfl
    · rw [ZFSet.mem_singleton] at ht
      subst t
      exact ZFSet.mem_union.2 (Or.inl ha)
    · rcases ZFSet.mem_pair.1 ht with rfl | rfl
      · exact ZFSet.mem_union.2 (Or.inl ha)
      · exact ZFSet.mem_union.2 (Or.inr hb)
  · exact smallAt_powerset hc (smallAt_powerset hc (smallAt_union hx hy))

theorem smallAt_funs {c : Cardinal.{u}} (hc : c.IsInaccessible)
    {x y : ZFSet.{u}} (hx : SmallAt c x) (hy : SmallAt c y) :
    SmallAt c (ZFSet.funs x y) := by
  exact smallAt_of_subset ZFSet.sep_subset (smallAt_powerset hc (smallAt_prod hc hx hy))

/-- Replacement for arbitrary metatheoretic functions, with definability hidden from clients. -/
noncomputable def repl (f : ZFSet.{u} → ZFSet.{u}) (x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range fun a : x => f a

@[simp]
theorem mem_repl {f : ZFSet.{u} → ZFSet.{u}} {x y : ZFSet.{u}} :
    y ∈ repl f x ↔ ∃ a ∈ x, f a = y := by
  simp [repl]

private theorem rank_repl (f : ZFSet.{u} → ZFSet.{u}) (x : ZFSet.{u}) :
    ZFSet.rank (repl f x) = ⨆ a : x, Order.succ (ZFSet.rank (f a)) := by
  simp [repl]

theorem smallAt_repl {c : Cardinal.{u}} (hc : c.IsInaccessible)
    {f : ZFSet.{u} → ZFSet.{u}} {x : ZFSet.{u}}
    (hx : SmallAt c x) (hf : ∀ a ∈ x, SmallAt c (f a)) : SmallAt c (repl f x) := by
  rw [smallAt_iff_rank_lt, rank_repl]
  apply Ordinal.lift_iSup_lt_of_lt_cof (a := c.ord)
  · rw [← Ordinal.lift_cof, hc.isRegular.cof_ord]
    have hcard : Cardinal.lift.{u + 1, u} (ZFSet.card x) < Cardinal.lift.{u + 1, u} c :=
      Cardinal.lift_lt.2 (card_lt_of_smallAt hc hx)
    simpa [ZFSet.cardinalMk_coe_sort] using hcard
  · intro a
    exact hc.ord_isSuccLimit.succ_lt
      (smallAt_iff_rank_lt.1 (hf a a.property))

/-- The graph of a function whose domain and values lie in an inaccessible stage also lies there. -/
theorem smallAt_graph {c : Cardinal.{u}} (hc : c.IsInaccessible)
    {f : ZFSet.{u} → ZFSet.{u}} {x : ZFSet.{u}}
    (hx : SmallAt c x) (hf : ∀ a ∈ x, SmallAt c (f a)) :
    SmallAt c (repl (fun a => ZFSet.pair a (f a)) x) := by
  apply smallAt_repl hc hx
  intro a ha
  exact smallAt_orderedPair hc (smallAt_mem ha hx) (hf a ha)

/-- Union of an arbitrary metatheoretic family indexed by a set. -/
noncomputable def boundedUnion (f : ZFSet.{u} → ZFSet.{u}) (x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sUnion (repl f x)

@[simp]
theorem mem_boundedUnion {f : ZFSet.{u} → ZFSet.{u}} {x y : ZFSet.{u}} :
    y ∈ boundedUnion f x ↔ ∃ a ∈ x, y ∈ f a := by
  simp [boundedUnion]

theorem smallAt_boundedUnion {c : Cardinal.{u}} (hc : c.IsInaccessible)
    {f : ZFSet.{u} → ZFSet.{u}} {x : ZFSet.{u}}
    (hx : SmallAt c x) (hf : ∀ a ∈ x, SmallAt c (f a)) :
    SmallAt c (boundedUnion f x) :=
  smallAt_sUnion (smallAt_repl hc hx hf)

end Lean4LeanModel
