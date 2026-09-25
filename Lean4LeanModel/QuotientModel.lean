import Lean4LeanModel.Quotient
import Lean4LeanModel.ModelSetup
import Lean4Lean.Theory.Typing.QuotLemmas

/-!
# Semantic meanings of Lean's quotient primitives

This module begins the bridge from the representation-independent quotient operations to the
primitive declarations installed by `VEnv.addQuot`: it validates the exact `Quot` type-former
declaration and states the canonical `Eq` and quotient-assignment invariants required by the
remaining constants and computation rule.
-/

namespace Lean4LeanModel

open Lean4Lean

universe u

/-- The semantic proposition obtained by applying the assigned interpretation of `Eq`. -/
noncomputable def assignedEqValue (assignment : Assignment.{u}) (n : Nat)
    (A a b : ZFSet.{u}) : ZFSet.{u} :=
  depApp (depApp (depApp (assignment.constVal ``Eq [n]) A) a) b

/-- Unfolding the interpretation of a fully applied `Eq` constant gives `assignedEqValue`.
The three hypotheses record that the constant and its two partial applications are data rather
than proofs; well-typed uses discharge them from the generated `Eq` declaration. -/
theorem interp_eq_app_eq_assignedEqValue {κ : ℕ → Cardinal.{u}} {env : VEnv}
    {assignment : Assignment.{u}} {L : List Nat} {Γ : List VExpr} {γ : List ZFSet.{u}}
    {l : VLevel} {A a b : VExpr}
    (hc₀ : safeTermClass env Γ L (VExpr.const ``Eq [l]) ≠ 0)
    (hc₁ : safeTermClass env Γ L ((VExpr.const ``Eq [l]).app A) ≠ 0)
    (hc₂ : safeTermClass env Γ L (((VExpr.const ``Eq [l]).app A).app a) ≠ 0) :
    interp κ env assignment L Γ γ ((((VExpr.const ``Eq [l]).app A).app a).app b) =
      assignedEqValue assignment (l.eval L)
        (interp κ env assignment L Γ γ A)
        (interp κ env assignment L Γ γ a)
        (interp κ env assignment L Γ γ b) := by
  simp only [interp_app, interp_const, hc₀, if_false, appValue, hc₁, hc₂,
    List.map, assignedEqValue]

/-- The precise invariant about the canonical `Eq` interpretation needed by genuine quotients.
The future inductive construction must establish this when it installs `Eq`; ordinary declaration
extensions then preserve it. -/
def Assignment.ModelsEq (κ : ℕ → Cardinal.{u}) (assignment : Assignment.{u}) : Prop :=
  ∀ n, ∀ A ∈ ModelUniverse κ n, ∀ a ∈ A, ∀ b ∈ A,
    assignedEqValue assignment n A a b = truthValue (a = b)

theorem Assignment.ModelsEq.congr {κ : ℕ → Cardinal.{u}}
    {assignment assignment' : Assignment.{u}} (hEq : assignment.ModelsEq κ)
    (h : ∀ ns, assignment'.constVal ``Eq ns = assignment.constVal ``Eq ns) :
    assignment'.ModelsEq κ := by
  intro n A hA a ha b hb
  simpa [assignedEqValue, h [n]] using hEq n A hA a ha b hb

/-- The assigned quotient type former and constructor are the genuine values constructed in
`Quotient`. This is the additional invariant needed when validating a later `Quot.sound` axiom. -/
def Assignment.ModelsQuot (κ : ℕ → Cardinal.{u}) (assignment : Assignment.{u}) : Prop :=
  (∀ n, assignment.constVal ``Quot [n] = quotTypeValue κ n) ∧
  (∀ n, assignment.constVal ``Quot.mk [n] = quotMkConstValue κ n)

/-- The complete semantic assignment of all four quotient primitives. `ModelsQuot` is the prefix
available after installing `Quot` and `Quot.mk`; this stronger invariant describes the result of
the complete `addQuot` operation. -/
def Assignment.ModelsQuotPrimitives (κ : ℕ → Cardinal.{u})
    (assignment : Assignment.{u}) : Prop :=
  assignment.ModelsQuot κ ∧
  (∀ n m, assignment.constVal ``Quot.lift [n, m] = quotLiftConstValue κ n m) ∧
  (∀ n, assignment.constVal ``Quot.ind [n] = quotIndConstValue)

theorem Assignment.ModelsQuot.congr {κ : ℕ → Cardinal.{u}}
    {assignment assignment' : Assignment.{u}} (hQuot : assignment.ModelsQuot κ)
    (h : ∀ c ns, c = ``Quot ∨ c = ``Quot.mk →
      assignment'.constVal c ns = assignment.constVal c ns) :
    assignment'.ModelsQuot κ := by
  constructor
  · intro n
    rw [h ``Quot [n] (Or.inl rfl)]
    exact hQuot.1 n
  · intro n
    rw [h ``Quot.mk [n] (Or.inr rfl)]
    exact hQuot.2 n

theorem Assignment.ModelsQuotPrimitives.congr {κ : ℕ → Cardinal.{u}}
    {assignment assignment' : Assignment.{u}} (hQuot : assignment.ModelsQuotPrimitives κ)
    (h : ∀ c ns,
      c = ``Quot ∨ c = ``Quot.mk ∨ c = ``Quot.lift ∨ c = ``Quot.ind →
      assignment'.constVal c ns = assignment.constVal c ns) :
    assignment'.ModelsQuotPrimitives κ := by
  refine ⟨hQuot.1.congr fun c ns hc => h c ns (hc.elim Or.inl fun h => Or.inr (Or.inl h)), ?_, ?_⟩
  · intro n m
    rw [h ``Quot.lift [n, m] (Or.inr (Or.inr (Or.inl rfl)))]
    exact hQuot.2.1 n m
  · intro n
    rw [h ``Quot.ind [n] (Or.inr (Or.inr (Or.inr rfl)))]
    exact hQuot.2.2 n

/-- The exact nested proposition used for the interpreted respect argument of `Quot.lift`.
Unlike `QuotientRespects`, this keeps the proof of `r a b` as a semantic binder, just as the
lean4lean expression does. -/
noncomputable def quotLiftRespectValue (assignment : Assignment.{u}) (m : Nat)
    (A r B f : ZFSet.{u}) : ZFSet.{u} :=
  forallValue A fun a =>
    forallValue A fun b =>
      forallValue (depApp (depApp r a) b) fun _ =>
        assignedEqValue assignment m B (appValue m f a) (appValue m f b)

/-- Under the canonical interpretation of equality, the exact semantic type of the
`Quot.lift` respect proof is the truth value of the metatheoretic respect condition. -/
theorem quotRespectsType_eq {κ : ℕ → Cardinal.{u}}
    {assignment : Assignment.{u}} (hEq : assignment.ModelsEq κ)
    {m : Nat} {A r B f : ZFSet.{u}} (hr : r ∈ relationSpace A)
    (hB : B ∈ ModelUniverse κ m) (hf : f ∈ piValue m A (fun _ => B)) :
    quotLiftRespectValue assignment m A r B f =
      truthValue (QuotientRespects m A (relationOfGraph r) f) := by
  simp only [quotLiftRespectValue, forallValue, bullet_mem_truthValue]
  apply congrArg truthValue
  apply propext
  constructor
  · intro h a ha b hb hab
    have hfa : appValue m f a ∈ B := appValue_mem hf ha
    have hfb : appValue m f b ∈ B := appValue_mem hf hb
    have heq := h a ha b hb bullet hab
    rw [hEq m B hB (appValue m f a) hfa (appValue m f b) hfb,
      bullet_mem_truthValue] at heq
    exact heq
  · intro h a ha b hb p hp
    have hpProp : depApp (depApp r a) b ∈ (propUniverse : ZFSet.{u}) :=
      relationOfGraph_mem_prop hr ha hb
    have hpEq : p = bullet := eq_bullet_of_mem_prop hpProp hp
    subst p
    have hfa : appValue m f a ∈ B := appValue_mem hf ha
    have hfb : appValue m f b ∈ B := appValue_mem hf hb
    rw [hEq m B hB (appValue m f a) hfa (appValue m f b) hfb,
      bullet_mem_truthValue]
    exact h a ha b hb hp

/-- Canonical equality turns the interpreted respect premise of `Quot.lift` into the
metatheoretic equality condition used by `quotLiftConstValue`. -/
theorem quotientRespects_of_modelsEq {κ : ℕ → Cardinal.{u}}
    {assignment : Assignment.{u}} (hEq : assignment.ModelsEq κ)
    {m : Nat} {A B r f : ZFSet.{u}} (hB : B ∈ ModelUniverse κ m)
    (hf : f ∈ piValue m A (fun _ => B))
    (h : ∀ a ∈ A, ∀ b ∈ A, relationOfGraph r a b →
      bullet ∈ assignedEqValue assignment m B (appValue m f a) (appValue m f b)) :
    QuotientRespects m A (relationOfGraph r) f := by
  intro a ha b hb hab
  have hfa : appValue m f a ∈ B := appValue_mem hf ha
  have hfb : appValue m f b ∈ B := appValue_mem hf hb
  have heq := h a ha b hb hab
  rw [hEq m B hB (appValue m f a) hfa (appValue m f b) hfb,
    bullet_mem_truthValue] at heq
  exact heq

/-- `Quot.sound` is valid for the genuine quotient whenever `Eq` has its canonical meaning. -/
theorem quotSound_semantic {κ : ℕ → Cardinal.{u}} {assignment : Assignment.{u}}
    (hi : ∀ n, (κ n).IsInaccessible) (hEq : assignment.ModelsEq κ)
    {n : Nat} {A r a b : ZFSet.{u}}
    (hA : A ∈ ModelUniverse κ n) (ha : a ∈ A) (hb : b ∈ A)
    (hab : relationOfGraph r a b) :
    bullet ∈ assignedEqValue assignment n (quotValue n A (relationOfGraph r))
      (quotMkValue n A (relationOfGraph r) a)
      (quotMkValue n A (relationOfGraph r) b) := by
  rw [hEq n (quotValue n A (relationOfGraph r))
    (quotValue_mem_ModelUniverse hi hA)
    (quotMkValue n A (relationOfGraph r) a) (quotMkValue_mem ha)
    (quotMkValue n A (relationOfGraph r) b) (quotMkValue_mem hb)]
  rw [bullet_mem_truthValue]
  exact quotMkValue_sound ha hb hab

theorem quotConstValue_valid {κ : ℕ → Cardinal.{u}} {env : VEnv}
    {assignment : Assignment.{u}} (henv : env.WF)
    (hi : ∀ n, (κ n).IsInaccessible) (n : Nat) :
    quotTypeValue κ n ∈ interp κ env assignment [n] [] [] quotConst.type := by
  let α : VExpr := .sort (.param 0)
  let rel : VExpr := .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))
  have hα : env.IsType 1 [] α := by
    refine ⟨.succ (.param 0), ?_⟩
    exact .sort (by decide)
  have hΓα : OnCtx [α] (env.IsType 1) := ⟨trivial, hα⟩
  have hrel : env.IsType 1 [α] rel := by
    refine ⟨.imax (.param 0) (.imax (.param 0) (.succ .zero)), ?_⟩
    simp only [rel]
    apply VEnv.HasType.forallE
    · type_tac
    · apply VEnv.HasType.forallE
      · type_tac
      · exact .sort trivial
  have hΓrel : OnCtx [rel, α] (env.IsType 1) := ⟨hΓα, hrel⟩
  have hα' : env.IsType 1 [rel, α] α := by
    exact ⟨.succ (.param 0), .sort (by decide)⟩
  have hb0 : env.IsType 1 [α] (.bvar 0) := by
    exact ⟨.param 0, by type_tac⟩
  have hΓb0 : OnCtx [.bvar 0, α] (env.IsType 1) := ⟨hΓα, hb0⟩
  have hb1 : env.IsType 1 [.bvar 0, α] (.bvar 1) := by
    exact ⟨.param 0, by type_tac⟩
  have hΓb1 : OnCtx [.bvar 1, .bvar 0, α] (env.IsType 1) := ⟨hΓb0, hb1⟩
  have hrelBody : env.IsType 1 [.bvar 1, .bvar 0, α] (.sort .zero) := by
    exact ⟨.succ .zero, .sort trivial⟩
  have hcResult : safeTypeClass env [rel, α] [n] α ≠ 0 := by
    exact safeTypeClass_sort_ne_zero henv hΓrel (.param 0) Nat.zero_lt_one
  have hcRelInner :
      safeTypeClass env [.bvar 1, .bvar 0, α] [n] (.sort .zero) ≠ 0 := by
    exact safeTypeClass_sort_ne_zero henv hΓb1 .zero trivial
  have hcRelOuter :
      safeTypeClass env [.bvar 0, α] [n] (.forallE (.bvar 1) (.sort .zero)) ≠ 0 := by
    rw [safeTypeClass_forallE_eq (L := [n]) (Γ := [.bvar 0, α])
      henv hΓb0 hb1 hrelBody]
    exact hcRelInner
  have hcOuter : safeTypeClass env [α] [n] (.forallE rel α) ≠ 0 := by
    rw [safeTypeClass_forallE_eq (L := [n]) (Γ := [α])
      henv hΓα hrel hα']
    exact hcResult
  change quotTypeValue κ n ∈
    interp κ env assignment [n] [] [] (.forallE α (.forallE rel α))
  simp only [interp_forallE, piValue, hcOuter, hcResult, if_false]
  simp only [α, rel, interp_sort, interp_forallE, interp_bvar, piValue,
    hcRelOuter, hcRelInner, if_false, List.getD_cons_zero, List.getD_cons_succ]
  change quotTypeValue κ n ∈ depFuns (ModelUniverse κ n) fun A =>
    depFuns (relationSpace A) fun _ => ModelUniverse κ n
  exact quotTypeValue_mem hi n

/-- The constructed interpretation of `Quot.mk` inhabits lean4lean's exact primitive type once
the preceding `Quot` declaration has been installed with its genuine semantic value. -/
theorem quotMkConstValue_valid {κ : ℕ → Cardinal.{u}} {env : VEnv}
    {assignment : Assignment.{u}} (henv : env.WF)
    (hQuotDecl : env.constants ``Quot = some quotConst)
    (hQuot : ∀ n, assignment.constVal ``Quot [n] = quotTypeValue κ n) (n : Nat) :
    quotMkConstValue κ n ∈ interp κ env assignment [n] [] [] quotMkConst.type := by
  let α : VExpr := .sort (.param 0)
  let rel : VExpr := .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))
  let q : VExpr := ((VExpr.const ``Quot [.param 0]).app (.bvar 2)).app (.bvar 1)
  let Γa : List VExpr := [.bvar 1, rel, α]
  let qc : VExpr := .const ``Quot [.param 0]
  let relA : VExpr := .forallE (.bvar 2) (.forallE (.bvar 3) (.sort .zero))
  let qAType : VExpr := .forallE relA (.sort (.param 0))
  let qA : VExpr := qc.app (.bvar 2)
  let lrel : VLevel := .imax (.param 0) (.imax (.param 0) (.succ .zero))
  let lqA : VLevel := .imax lrel (.succ (.param 0))
  let lqc : VLevel := .imax (.succ (.param 0)) lqA
  have hqAr : env.HasType 1 Γa q (.sort (.param 0)) := by
    simp only [q]
    type_tac
  have hα : env.IsType 1 [] α := ⟨.succ (.param 0), by simp only [α]; type_tac⟩
  have hΓα : OnCtx [α] (env.IsType 1) := ⟨trivial, hα⟩
  have hrel : env.IsType 1 [α] rel := by
    refine ⟨lrel, ?_⟩
    simp only [rel]
    apply VEnv.HasType.forallE
    · type_tac
    · apply VEnv.HasType.forallE
      · type_tac
      · exact .sort trivial
  have hΓrel : OnCtx [rel, α] (env.IsType 1) := ⟨hΓα, hrel⟩
  have ha : env.HasType 1 [rel, α] (.bvar 1) (.sort (.param 0)) := by type_tac
  have hΓa : OnCtx Γa (env.IsType 1) := ⟨hΓrel, ⟨.param 0, ha⟩⟩
  have hqc : env.HasType 1 Γa qc (quotConst.type.instL [.param 0]) := by
    exact VEnv.HasType.const hQuotDecl (by decide) (by decide)
  have hqcTy : env.HasType 1 Γa (quotConst.type.instL [.param 0])
      (.sort lqc) := by
    simpa [quotConst, VExpr.instL, VLevel.inst] using (show env.HasType 1 Γa
      (.forallE (.sort (.param 0))
        (.forallE (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))
          (.sort (.param 0))))
      (.sort lqc) from by
        simp only [lqc, lqA, lrel]
        apply VEnv.HasType.forallE
        · exact .sort (by decide)
        · apply VEnv.HasType.forallE
          · apply VEnv.HasType.forallE
            · type_tac
            · apply VEnv.HasType.forallE
              · type_tac
              · exact .sort trivial
          · exact .sort (by decide))
  have hcQc : safeTermClass env Γa [n] qc ≠ 0 :=
    safeTermClass_ne_zero_of_hasType henv hΓa hqc hqcTy
      (by simp [lqc, lqA, lrel, VLevel.eval, Nat.imax])
  have hqA : env.HasType 1 Γa qA qAType := by
    simp only [qA, qAType, relA, qc]
    type_tac
  have hqATy : env.HasType 1 Γa qAType (.sort lqA) := by
    simp only [qAType, relA]
    simp only [lqA, lrel]
    apply VEnv.HasType.forallE
    · apply VEnv.HasType.forallE
      · type_tac
      · apply VEnv.HasType.forallE
        · type_tac
        · exact .sort trivial
    · exact .sort (by decide)
  have hcQA : safeTermClass env Γa [n] qA ≠ 0 :=
    safeTermClass_ne_zero_of_hasType henv hΓa hqA hqATy
      (by simp [lqA, lrel, VLevel.eval, Nat.imax])
  have hcQ : safeTypeClass env Γa [n] q = 0 ↔ n = 0 := by
    change safeTypeClass env Γa [n] q = 0 ↔ n = 0
    rw [safeTypeClass_eq hΓa,
      typeClass_eq_zero_iff_of_hasType (L := [n]) henv hΓa hqAr]
    simp [VLevel.eval]
  have hinner : env.IsType 1 [rel, α] (.forallE (.bvar 1) q) := by
    exact ⟨.imax (.param 0) (.param 0), .forallE ha hqAr⟩
  have hcInner : safeTypeClass env [rel, α] [n] (.forallE (.bvar 1) q) = 0 ↔ n = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n]) (Γ := [rel, α])
      henv hΓrel ⟨.param 0, ha⟩ ⟨.param 0, hqAr⟩]
    exact hcQ
  have hcOuter : safeTypeClass env [α] [n] (.forallE rel (.forallE (.bvar 1) q)) = 0 ↔
      n = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n]) (Γ := [α]) henv hΓα hrel hinner]
    exact hcInner
  have hcRelInner :
      safeTypeClass env [.bvar 1, .bvar 0, α] [n] (.sort .zero) ≠ 0 := by
    have hΓb0 : OnCtx [.bvar 0, α] (env.IsType 1) :=
      ⟨hΓα, ⟨.param 0, by type_tac⟩⟩
    have hΓb1 : OnCtx [.bvar 1, .bvar 0, α] (env.IsType 1) :=
      ⟨hΓb0, ⟨.param 0, by type_tac⟩⟩
    exact safeTypeClass_sort_ne_zero (L := [n]) henv hΓb1 .zero trivial
  have hcRelOuter :
      safeTypeClass env [.bvar 0, α] [n] (.forallE (.bvar 1) (.sort .zero)) ≠ 0 := by
    have hb0 : env.IsType 1 [α] (.bvar 0) := ⟨.param 0, by type_tac⟩
    have hΓb0 : OnCtx [.bvar 0, α] (env.IsType 1) := ⟨hΓα, hb0⟩
    have hb1 : env.IsType 1 [.bvar 0, α] (.bvar 1) := ⟨.param 0, by type_tac⟩
    have hbody : env.IsType 1 [.bvar 1, .bvar 0, α] (.sort .zero) :=
      ⟨.succ .zero, .sort trivial⟩
    rw [safeTypeClass_forallE_eq (L := [n]) henv hΓb0 hb1 hbody]
    exact hcRelInner
  change quotMkConstValue κ n ∈ interp κ env assignment [n] [] []
    (.forallE α (.forallE rel (.forallE (.bvar 1) q)))
  simp only [interp_forallE, α, rel, q, interp_sort, interp_bvar, interp_app, interp_const]
  have hcInner' := hcInner
  have hcQ' := hcQ
  have hcQc' := hcQc
  have hcQA' := hcQA
  simp only [rel, α, q, Γa, qc, qA] at hcInner' hcQ' hcQc' hcQA'
  rw [piValue_congr_zero hcOuter]
  simp_rw [piValue_congr_zero hcInner', piValue_congr_zero hcQ']
  simp only [interpLevel, List.getD_cons_zero, List.getD_cons_succ]
  have hcRelOuter' := hcRelOuter
  have hcRelInner' := hcRelInner
  simp only [α] at hcRelOuter' hcRelInner'
  have hrelation (A : ZFSet.{u}) :
      piValue (safeTypeClass env [.bvar 0, .sort (.param 0)] [n]
          (.forallE (.bvar 1) (.sort .zero))) A (fun _ =>
        piValue (safeTypeClass env [.bvar 1, .bvar 0, .sort (.param 0)] [n]
          (.sort .zero)) A (fun _ => propUniverse)) = relationSpace A := by
    simp only [piValue, if_neg hcRelOuter', if_neg hcRelInner', relationSpace]
  simp only [VLevel.eval, ModelUniverse_zero]
  simp_rw [hrelation]
  simp only [hcQc', hcQA', if_false, appValue, List.map, VLevel.eval,
    List.getD_cons_zero, hQuot]
  convert quotMkConstValue_mem (κ := κ) n using 1
  apply piValue_congr
  intro A hA
  apply piValue_congr
  intro r hr
  apply piValue_congr
  intro _ _
  simp only [quotTypeValue]
  rw [depApp_depLam hA, depApp_depLam hr]

end Lean4LeanModel
