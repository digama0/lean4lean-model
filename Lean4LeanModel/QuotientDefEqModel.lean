import Lean4LeanModel.QuotientLiftModel

/-! # The quotient computation rule -/

namespace Lean4LeanModel
open Lean4Lean
universe u

private theorem interp_lam_congr_of_hasType {κ : ℕ → Cardinal.{u}} {env : VEnv}
    {assignment : Assignment.{u}} {L : List Nat} {Γ : List VExpr} {γ : List ZFSet.{u}}
    {A body body' B : VExpr}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType L.length))
    (hA : env.IsType L.length Γ A)
    (hbody : env.HasType L.length (A :: Γ) body B)
    (hbody' : env.HasType L.length (A :: Γ) body' B)
    (hB : env.IsType L.length (A :: Γ) B)
    (h : ∀ x ∈ interp κ env assignment L Γ γ A,
      interp κ env assignment L (A :: Γ) (x :: γ) body =
        interp κ env assignment L (A :: Γ) (x :: γ) body') :
    interp κ env assignment L Γ γ (.lam A body) =
      interp κ env assignment L Γ γ (.lam A body') := by
  have hΓA : OnCtx (A :: Γ) (env.IsType L.length) := ⟨hΓ, hA⟩
  obtain ⟨v, hB⟩ := hB
  simp only [interp_lam]
  rw [safeTermClass_eq hΓA, safeTermClass_eq hΓA,
    termClass_eq_typeClass_of_hasType henv hΓA hbody hB,
    termClass_eq_typeClass_of_hasType henv hΓA hbody' hB]
  exact lamValue_congr h

set_option maxHeartbeats 350000

theorem quotDefEq_valid {κ : ℕ → Cardinal.{u}} {env : VEnv}
    {assignment : Assignment.{u}}
    (henv : env.WF)
    (hEqDecl : env.constants ``Eq = some eqConst)
    (hQuotDecl : env.constants ``Quot = some quotConst)
    (hMkDecl : env.constants ``Quot.mk = some quotMkConst)
    (hLiftDecl : env.constants ``Quot.lift = some quotLiftConst)
    (hEq : assignment.ModelsEq κ)
    (hQuot : assignment.ModelsQuotPrimitives κ)
    (n m : Nat) :
    interp κ env assignment [n, m] [] [] quotDefEq.lhs =
      interp κ env assignment [n, m] [] [] quotDefEq.rhs := by
  let α : VExpr := .sort (.param 0)
  let rel : VExpr := .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))
  let β : VExpr := .sort (.param 1)
  let fn : VExpr := .forallE (.bvar 2) (.bvar 1)
  let eqApp : VExpr :=
    (((VExpr.const ``Eq [.param 1]).app (.bvar 4)).app
      ((VExpr.bvar 3).app (.bvar 2))).app ((VExpr.bvar 3).app (.bvar 1))
  let rab : VExpr := ((VExpr.bvar 4).app (.bvar 1)).app (.bvar 0)
  let respect : VExpr := .forallE (.bvar 3) <| .forallE (.bvar 4) <|
    .forallE rab eqApp
  let liftApp : VExpr := ((((((VExpr.const ``Quot.lift [.param 0, .param 1]).app
    (.bvar 5)).app (.bvar 4)).app (.bvar 3)).app (.bvar 2)).app (.bvar 1))
  let mkApp : VExpr := (((VExpr.const ``Quot.mk [.param 0]).app
    (.bvar 5)).app (.bvar 4)).app (.bvar 0)
  let lhsBody : VExpr := liftApp.app mkApp
  let rhsBody : VExpr := (VExpr.bvar 2).app (.bvar 0)
  let lhsC : VExpr := .lam (.bvar 4) lhsBody
  let rhsC : VExpr := .lam (.bvar 4) rhsBody
  let lhsF : VExpr := .lam respect lhsC
  let rhsF : VExpr := .lam respect rhsC
  let lhsB : VExpr := .lam fn lhsF
  let rhsB : VExpr := .lam fn rhsF
  let lhsR : VExpr := .lam β lhsB
  let rhsR : VExpr := .lam β rhsB
  let lhsA : VExpr := .lam rel lhsR
  let rhsA : VExpr := .lam rel rhsR
  let result : VExpr := .forallE (.bvar 4) (.bvar 3)
  let bodyC : VExpr := .forallE respect result
  let bodyF : VExpr := .forallE fn bodyC
  let bodyB : VExpr := .forallE β bodyF
  let bodyR : VExpr := .forallE rel bodyB
  let Γα := [α]
  let Γr := [rel, α]
  let Γβ := [β, rel, α]
  let Γf := [fn, β, rel, α]
  let Γc := [respect, fn, β, rel, α]
  let Γa := [.bvar 4, respect, fn, β, rel, α]
  have hα : env.IsType 2 [] α := ⟨?_, by simp only [α]; type_tac⟩
  have hΓα : OnCtx Γα (env.IsType 2) := ⟨trivial, hα⟩
  have hrel : env.IsType 2 Γα rel :=
    ⟨?_, by simp only [Γα, rel, α]; type_tac⟩
  have hΓr : OnCtx Γr (env.IsType 2) := ⟨hΓα, hrel⟩
  have hβ : env.IsType 2 Γr β :=
    ⟨?_, by simp only [Γr, β, rel, α]; type_tac⟩
  have hΓβ : OnCtx Γβ (env.IsType 2) := ⟨hΓr, hβ⟩
  have hfn : env.IsType 2 Γβ fn :=
    ⟨?_, by simp only [Γβ, fn, β, rel, α]; type_tac⟩
  have hΓf : OnCtx Γf (env.IsType 2) := ⟨hΓβ, hfn⟩
  have hrespect : env.IsType 2 Γf respect :=
    ⟨?_, by simp only [Γf, respect, eqApp, rab, fn, β, rel, α]; type_tac⟩
  have hΓc : OnCtx Γc (env.IsType 2) := ⟨hΓf, hrespect⟩
  have haTy : env.IsType 2 Γc (.bvar 4) :=
    ⟨.param 0, by simp only [Γc, respect, eqApp, rab, fn, β, rel, α]; type_tac⟩
  have hΓa : OnCtx Γa (env.IsType 2) := ⟨hΓc, haTy⟩
  have hlhsBody : env.HasType 2 Γa lhsBody (.bvar 3) := by
    simp only [Γa, lhsBody, liftApp, mkApp, respect, eqApp, rab, fn, β, rel, α]
    type_tac
  have hrhsBody : env.HasType 2 Γa rhsBody (.bvar 3) := by
    simp only [Γa, rhsBody, respect, eqApp, rab, fn, β, rel, α]
    type_tac
  obtain ⟨ua, haHT⟩ := haTy
  obtain ⟨uc, hrespectHT⟩ := hrespect
  obtain ⟨uf, hfnHT⟩ := hfn
  obtain ⟨ub, hβHT⟩ := hβ
  obtain ⟨ur, hrelHT⟩ := hrel
  have hlhsC : env.HasType 2 Γc lhsC result := by
    exact VEnv.IsDefEq.lamDF haHT hlhsBody
  have hrhsC : env.HasType 2 Γc rhsC result := by
    exact VEnv.IsDefEq.lamDF haHT hrhsBody
  have hlhsF : env.HasType 2 Γf lhsF bodyC := by
    exact VEnv.IsDefEq.lamDF hrespectHT hlhsC
  have hrhsF : env.HasType 2 Γf rhsF bodyC := by
    exact VEnv.IsDefEq.lamDF hrespectHT hrhsC
  have hlhsB : env.HasType 2 Γβ lhsB bodyF := by
    exact VEnv.IsDefEq.lamDF hfnHT hlhsF
  have hrhsB : env.HasType 2 Γβ rhsB bodyF := by
    exact VEnv.IsDefEq.lamDF hfnHT hrhsF
  have hlhsR : env.HasType 2 Γr lhsR bodyB := by
    exact VEnv.IsDefEq.lamDF hβHT hlhsB
  have hrhsR : env.HasType 2 Γr rhsR bodyB := by
    exact VEnv.IsDefEq.lamDF hβHT hrhsB
  have hlhsA : env.HasType 2 Γα lhsA bodyR := by
    exact VEnv.IsDefEq.lamDF hrelHT hlhsR
  have hrhsA : env.HasType 2 Γα rhsA bodyR := by
    exact VEnv.IsDefEq.lamDF hrelHT hrhsR
  have hbodyR : env.IsType 2 Γα bodyR :=
    ⟨?_, by simp only [Γα, bodyR, bodyB, bodyF, bodyC, result,
      respect, eqApp, rab, fn, β, rel, α]; type_tac⟩
  have hbodyB : env.IsType 2 Γr bodyB :=
    ⟨?_, by simp only [Γr, bodyB, bodyF, bodyC, result,
      respect, eqApp, rab, fn, β, rel, α]; type_tac⟩
  have hbodyF : env.IsType 2 Γβ bodyF :=
    ⟨?_, by simp only [Γβ, bodyF, bodyC, result,
      respect, eqApp, rab, fn, β, rel, α]; type_tac⟩
  have hbodyC : env.IsType 2 Γf bodyC :=
    ⟨?_, by simp only [Γf, bodyC, result,
      respect, eqApp, rab, fn, β, rel, α]; type_tac⟩
  have hresult : env.IsType 2 Γc result :=
    ⟨?_, by simp only [Γc, result, respect, eqApp, rab, fn, β, rel, α]; type_tac⟩
  have hresHT : env.HasType 2 Γa (.bvar 3) (.sort (.param 1)) := by
    simp only [Γa, respect, eqApp, rab, fn, β, rel, α]; type_tac
  have hres : env.IsType 2 Γa (.bvar 3) := ⟨.param 1, hresHT⟩
  have hcRes : safeTypeClass env Γa [n, m] (.bvar 3) = 0 ↔ m = 0 := by
    rw [safeTypeClass_eq hΓa,
      typeClass_eq_zero_iff_of_hasType (L := [n, m]) henv hΓa hresHT]
    simp [VLevel.eval]
  have hcResult : safeTypeClass env Γc [n, m] result = 0 ↔ m = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n, m]) (Γ := Γc) henv hΓc ⟨ua, haHT⟩ hres]
    exact hcRes
  have hcBodyC : safeTypeClass env Γf [n, m] bodyC = 0 ↔ m = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n, m]) (Γ := Γf) henv hΓf
      ⟨uc, hrespectHT⟩ hresult]
    exact hcResult
  have hcBodyF : safeTypeClass env Γβ [n, m] bodyF = 0 ↔ m = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n, m]) (Γ := Γβ) henv hΓβ ⟨uf, hfnHT⟩ hbodyC]
    exact hcBodyC
  have hcBodyB : safeTypeClass env Γr [n, m] bodyB = 0 ↔ m = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n, m]) (Γ := Γr) henv hΓr ⟨ub, hβHT⟩ hbodyF]
    exact hcBodyF
  have hcBodyR : safeTypeClass env Γα [n, m] bodyR = 0 ↔ m = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n, m]) (Γ := Γα) henv hΓα ⟨ur, hrelHT⟩ hbodyB]
    exact hcBodyB
  have hΓrelA : OnCtx [.bvar 0, α] (env.IsType 2) :=
    ⟨hΓα, ⟨.param 0, by simp only [α]; type_tac⟩⟩
  have hΓrelAB : OnCtx [.bvar 1, .bvar 0, α] (env.IsType 2) :=
    ⟨hΓrelA, ⟨.param 0, by simp only [α]; type_tac⟩⟩
  have hcRelInner : safeTypeClass env [.bvar 1, .bvar 0, α]
      [n, m] (.sort .zero) ≠ 0 := safeTypeClass_sort_ne_zero henv hΓrelAB .zero trivial
  have hcRelOuter : safeTypeClass env [.bvar 0, α] [n, m]
      (.forallE (.bvar 1) (.sort .zero)) ≠ 0 := by
    rw [safeTypeClass_forallE_eq (L := [n, m]) (Γ := [.bvar 0, α]) henv hΓrelA
      (show env.IsType 2 [.bvar 0, α] (.bvar 1) from ⟨.param 0, by type_tac⟩)
      (show env.IsType 2 [.bvar 1, .bvar 0, α] (.sort .zero) from
        ⟨.succ .zero, .sort trivial⟩)]
    exact hcRelInner
  have hrelation (A : ZFSet.{u}) :
      interp κ env assignment [n, m] [α] [A] rel = relationSpace A := by
    simp only [rel, interp_forallE, interp_sort, interpLevel, VLevel.eval,
      List.getD_cons_zero, interp_bvar, ModelUniverse_zero]
    simp only [piValue, if_neg hcRelOuter, if_neg hcRelInner, relationSpace,
      List.getD_cons_succ]
    simp only [List.getD_cons_zero]
  have hΓfnA : OnCtx [.bvar 2, β, rel, α] (env.IsType 2) :=
    ⟨hΓβ, ⟨.param 0, by simp only [β, rel, α]; type_tac⟩⟩
  have hfnCodHT : env.HasType 2 [.bvar 2, β, rel, α] (.bvar 1)
      (.sort (.param 1)) := by simp only [β, rel, α]; type_tac
  have hcFnCod : safeTypeClass env [.bvar 2, β, rel, α]
      [n, m] (.bvar 1) = 0 ↔ m = 0 := by
    rw [safeTypeClass_eq hΓfnA,
      typeClass_eq_zero_iff_of_hasType (L := [n, m]) henv hΓfnA hfnCodHT]
    simp [VLevel.eval]
  let Γra := [.bvar 3, fn, β, rel, α]
  let Γrb := [.bvar 4, .bvar 3, fn, β, rel, α]
  let Γrh := [rab, .bvar 4, .bvar 3, fn, β, rel, α]
  have hraTy : env.IsType 2 Γf (.bvar 3) :=
    ⟨.param 0, by simp only [Γf, fn, β, rel, α]; type_tac⟩
  have hΓra : OnCtx Γra (env.IsType 2) := ⟨hΓf, hraTy⟩
  have hrbHT : env.HasType 2 Γra (.bvar 4) (.sort (.param 0)) := by
    simp only [Γra, fn, β, rel, α]; type_tac
  have hrbTy : env.IsType 2 Γra (.bvar 4) := ⟨.param 0, hrbHT⟩
  have hΓrb : OnCtx Γrb (env.IsType 2) := ⟨hΓra, hrbTy⟩
  have hrabHT : env.HasType 2 Γrb rab (.sort .zero) := by
    simp only [Γrb, rab, fn, β, rel, α]; type_tac
  have hrabTy : env.IsType 2 Γrb rab := ⟨.zero, hrabHT⟩
  have hΓrh : OnCtx Γrh (env.IsType 2) := ⟨hΓrb, hrabTy⟩
  have heqApp : env.HasType 2 Γrh eqApp (.sort .zero) := by
    simp only [Γrh, eqApp, rab, fn, β, rel, α]
    type_tac
  have hcEqApp : safeTypeClass env Γrh [n, m] eqApp = 0 := by
    rw [safeTypeClass_eq hΓrh]
    exact (typeClass_eq_zero_iff_of_hasType (L := [n, m]) henv hΓrh heqApp).2 rfl
  let respectH : VExpr := .forallE rab eqApp
  let respectB : VExpr := .forallE (.bvar 4) respectH
  have hrespectHHT : env.HasType 2 Γrb respectH
      (.sort (.imax .zero .zero)) := by
    simpa only [respectH] using VEnv.HasType.forallE hrabHT heqApp
  have hrespectHTy : env.IsType 2 Γrb respectH := ⟨_, hrespectHHT⟩
  have hcRespectH : safeTypeClass env Γrb [n, m] respectH = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n, m]) (Γ := Γrb) henv hΓrb hrabTy
      ⟨.zero, heqApp⟩]
    exact hcEqApp
  have hrespectBHT : env.HasType 2 Γra respectB
      (.sort (.imax (.param 0) (.imax .zero .zero))) := by
    simpa only [respectB] using VEnv.HasType.forallE hrbHT hrespectHHT
  have hrespectBTy : env.IsType 2 Γra respectB := ⟨_, hrespectBHT⟩
  have hcRespectB : safeTypeClass env Γra [n, m] respectB = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n, m]) (Γ := Γra) henv hΓra hrbTy hrespectHTy]
    exact hcRespectH
  have hcRespect : safeTypeClass env Γf [n, m] respect = 0 := by
    rw [show respect = .forallE (.bvar 3) respectB by
      simp only [respect, respectB, respectH]]
    rw [safeTypeClass_forallE_eq (L := [n, m]) (Γ := Γf) henv hΓf hraTy hrespectBTy]
    exact hcRespectB
  let lra : VLevel := .imax (.param 0) (.succ .zero)
  let relB : VExpr := .forallE (.bvar 5) (.forallE (.bvar 6) (.sort .zero))
  have hRVar : env.HasType 2 Γrb (.bvar 4) relB := by
    simp only [Γrb, relB, fn, β, rel, α]
    exact .bvar (by lookup_tac)
  let lrel : VLevel := .imax (.param 0) (.imax (.param 0) (.succ .zero))
  have hRelBTy : env.HasType 2 Γrb relB (.sort lrel) := by
    simp only [relB, lrel]
    apply VEnv.HasType.forallE
    · type_tac
    · apply VEnv.HasType.forallE
      · type_tac
      · exact .sort trivial
  have hcRVar : safeTermClass env Γrb [n, m] (.bvar 4) ≠ 0 :=
    safeTermClass_ne_zero_of_hasType henv hΓrb hRVar hRelBTy
      (by simp [lrel, VLevel.eval, Nat.imax])
  let rAType : VExpr := .forallE (.bvar 5) (.sort .zero)
  have hRA : env.HasType 2 Γrb ((VExpr.bvar 4).app (.bvar 1)) rAType := by
    simp only [Γrb, rAType, fn, β, rel, α]
    type_tac
  have hRATy : env.HasType 2 Γrb rAType (.sort lra) := by
    simp only [rAType, lra]
    apply VEnv.HasType.forallE
    · type_tac
    · exact .sort trivial
  have hcRA : safeTermClass env Γrb [n, m]
      ((VExpr.bvar 4).app (.bvar 1)) ≠ 0 :=
    safeTermClass_ne_zero_of_hasType henv hΓrb hRA hRATy (by simp [lra, VLevel.eval, Nat.imax])
  let lfn : VLevel := .imax (.param 0) (.param 1)
  let fnH : VExpr := fn.lift.lift.lift.lift
  have hFVar : env.HasType 2 Γrh (.bvar 3) fnH := by
    simp only [Γrh, fnH, rab, fn, β, rel, α]
    exact .bvar (by lookup_tac)
  have hFnHTy : env.HasType 2 Γrh fnH (.sort lfn) := by
    simp only [fnH, fn, lfn]
    apply VEnv.HasType.forallE <;> type_tac
  have hcFVar : safeTermClass env Γrh [n, m] (.bvar 3) = 0 ↔ m = 0 := by
    rw [safeTermClass_eq_zero_iff_of_hasType (L := [n, m]) henv hΓrh hFVar hFnHTy]
    cases m <;> simp [lfn, VLevel.eval, Nat.imax]
  let eqc : VExpr := .const ``Eq [.param 1]
  let lEqTail : VLevel := .imax (.param 1) (.succ .zero)
  let lEqB : VLevel := .imax (.param 1) lEqTail
  let lEqc : VLevel := .imax (.succ (.param 1)) lEqB
  have hEqc : env.HasType 2 Γrh eqc (eqConst.type.instL [.param 1]) :=
    VEnv.HasType.const (U := 2) hEqDecl (by decide) (by decide)
  have hEqcTy : env.HasType 2 Γrh (eqConst.type.instL [.param 1]) (.sort lEqc) := by
    simpa [eqConst, VExpr.instL, VLevel.inst] using (show env.HasType 2 Γrh
      (.forallE (.sort (.param 1))
        (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))))
      (.sort lEqc) from by
        simp only [lEqc, lEqB, lEqTail]
        apply VEnv.HasType.forallE
        · exact .sort (by decide)
        · apply VEnv.HasType.forallE
          · type_tac
          · apply VEnv.HasType.forallE
            · type_tac
            · exact .sort trivial)
  have hcEqc : safeTermClass env Γrh [n, m] eqc ≠ 0 :=
    safeTermClass_ne_zero_of_hasType henv hΓrh hEqc hEqcTy
      (by simp [lEqc, lEqB, lEqTail, VLevel.eval, Nat.imax])
  let eqB : VExpr := eqc.app (.bvar 4)
  let eqBType : VExpr := .forallE (.bvar 4) (.forallE (.bvar 5) (.sort .zero))
  have hEqB : env.HasType 2 Γrh eqB eqBType := by
    simp only [Γrh, eqB, eqBType, eqc, rab, fn, β, rel, α]
    type_tac
  have hEqBTy : env.HasType 2 Γrh eqBType (.sort lEqB) := by
    simp only [eqBType, lEqB, lEqTail]
    apply VEnv.HasType.forallE
    · type_tac
    · apply VEnv.HasType.forallE
      · type_tac
      · exact .sort trivial
  have hcEqB : safeTermClass env Γrh [n, m] eqB ≠ 0 :=
    safeTermClass_ne_zero_of_hasType henv hΓrh hEqB hEqBTy
      (by simp [lEqB, lEqTail, VLevel.eval, Nat.imax])
  let fa : VExpr := (VExpr.bvar 3).app (.bvar 2)
  let eqBa : VExpr := eqB.app fa
  let eqBaType : VExpr := .forallE (.bvar 4) (.sort .zero)
  have hEqBa : env.HasType 2 Γrh eqBa eqBaType := by
    simp only [Γrh, eqBa, eqBaType, eqB, fa, eqc, rab, fn, β, rel, α]
    type_tac
  have hEqBaTy : env.HasType 2 Γrh eqBaType (.sort lEqTail) := by
    simp only [eqBaType, lEqTail]
    apply VEnv.HasType.forallE
    · type_tac
    · exact .sort trivial
  have hcEqBa : safeTermClass env Γrh [n, m] eqBa ≠ 0 :=
    safeTermClass_ne_zero_of_hasType henv hΓrh hEqBa hEqBaTy
      (by simp [lEqTail, VLevel.eval, Nat.imax])
  have hrespectInterp (A r B f : ZFSet.{u}) :
      interp κ env assignment [n, m] [fn, β, rel, α] [f, B, r, A] respect =
        quotLiftRespectValue assignment m A r B f := by
    simp only [respect, interp_forallE]
    have hcRespectB' := hcRespectB
    have hcRespectH' := hcRespectH
    have hcEqApp' := hcEqApp
    simp only [Γra, respectB, respectH] at hcRespectB'
    simp only [Γrb, respectH] at hcRespectH'
    simp only [Γrh] at hcEqApp'
    simp_rw [hcRespectB', hcRespectH', hcEqApp']
    simp only [piValue, if_true]
    simp only [rab, interp_app, interp_bvar]
    have hcRVar' := hcRVar
    have hcRA' := hcRA
    simp only [Γrb] at hcRVar' hcRA'
    simp only [hcRVar', hcRA', if_false, appValue, List.getD_cons_zero,
      List.getD_cons_succ]
    simp only [eqApp, interp_app, interp_const, interp_bvar]
    have hcEqc' := hcEqc
    have hcEqB' := hcEqB
    have hcEqBa' := hcEqBa
    have hcFVar' := hcFVar
    simp only [Γrh, rab, eqc, eqB, eqBa, fa] at hcEqc' hcEqB' hcEqBa' hcFVar'
    simp only [hcEqc', hcEqB', hcEqBa', if_false, appValue,
      List.map, VLevel.eval, List.getD_cons_zero, List.getD_cons_succ]
    have happF (x : ZFSet.{u}) :
        (if safeTermClass env
            [((VExpr.bvar 4).app (.bvar 1)).app (.bvar 0), .bvar 4, .bvar 3,
              fn, β, rel, α] [n, m] (.bvar 3) = 0 then bullet else depApp f x) =
          appValue m f x := by
      change appValue (safeTermClass env
        [((VExpr.bvar 4).app (.bvar 1)).app (.bvar 0), .bvar 4, .bvar 3,
          fn, β, rel, α] [n, m] (.bvar 3)) f x = appValue m f x
      exact appValue_congr_zero hcFVar' f x
    simp_rw [happF]
    rfl
  let liftc : VExpr := .const ``Quot.lift [.param 0, .param 1]
  let liftA0 : VExpr := liftc.app (.bvar 0)
  let liftR0 : VExpr := liftA0.lift.app (.bvar 0)
  let liftB0 : VExpr := liftR0.lift.app (.bvar 0)
  let liftF0 : VExpr := liftB0.lift.app (.bvar 0)
  let liftC0 : VExpr := liftF0.lift.app (.bvar 0)
  let liftQuot : VExpr := ((VExpr.const ``Quot [.param 0]).app (.bvar 4)).app (.bvar 3)
  let liftResult : VExpr := .forallE liftQuot (.bvar 3)
  let liftBodyC : VExpr := .forallE respect liftResult
  let liftBodyF : VExpr := .forallE fn liftBodyC
  let liftBodyB : VExpr := .forallE β liftBodyF
  let liftBodyR : VExpr := .forallE rel liftBodyB
  let liftType : VExpr := .forallE α liftBodyR
  let Γq := [liftQuot, respect, fn, β, rel, α]
  have hliftQuot : env.IsType 2 Γc liftQuot :=
    ⟨?_, by simp only [Γc, liftQuot, respect, eqApp, rab, fn, β, rel, α]; type_tac⟩
  have hΓq : OnCtx Γq (env.IsType 2) := ⟨hΓc, hliftQuot⟩
  have hliftResHT : env.HasType 2 Γq (.bvar 3) (.sort (.param 1)) := by
    simp only [Γq, liftQuot, respect, eqApp, rab, fn, β, rel, α]; type_tac
  have hliftRes : env.IsType 2 Γq (.bvar 3) := ⟨.param 1, hliftResHT⟩
  have hliftResult : env.IsType 2 Γc liftResult :=
    ⟨?_, by simp only [Γc, liftResult, liftQuot, respect, eqApp, rab,
      fn, β, rel, α]; type_tac⟩
  have hliftBodyC : env.IsType 2 Γf liftBodyC :=
    ⟨?_, by simp only [Γf, liftBodyC, liftResult, liftQuot, respect, eqApp, rab,
      fn, β, rel, α]; type_tac⟩
  have hliftBodyF : env.IsType 2 Γβ liftBodyF :=
    ⟨?_, by simp only [Γβ, liftBodyF, liftBodyC, liftResult, liftQuot,
      respect, eqApp, rab, fn, β, rel, α]; type_tac⟩
  have hliftBodyB : env.IsType 2 Γr liftBodyB :=
    ⟨?_, by simp only [Γr, liftBodyB, liftBodyF, liftBodyC, liftResult, liftQuot,
      respect, eqApp, rab, fn, β, rel, α]; type_tac⟩
  have hliftBodyR : env.IsType 2 Γα liftBodyR :=
    ⟨?_, by simp only [Γα, liftBodyR, liftBodyB, liftBodyF, liftBodyC, liftResult,
      liftQuot, respect, eqApp, rab, fn, β, rel, α]; type_tac⟩
  have hcLiftRes : safeTypeClass env Γq [n, m] (.bvar 3) = 0 ↔ m = 0 := by
    rw [safeTypeClass_eq hΓq,
      typeClass_eq_zero_iff_of_hasType (L := [n, m]) henv hΓq hliftResHT]
    simp [VLevel.eval]
  have hcLiftResult : safeTypeClass env Γc [n, m] liftResult = 0 ↔ m = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n, m]) (Γ := Γc) henv hΓc hliftQuot hliftRes]
    exact hcLiftRes
  have hcLiftBodyC : safeTypeClass env Γf [n, m] liftBodyC = 0 ↔ m = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n, m]) (Γ := Γf) henv hΓf
      ⟨uc, hrespectHT⟩ hliftResult]
    exact hcLiftResult
  have hcLiftBodyF : safeTypeClass env Γβ [n, m] liftBodyF = 0 ↔ m = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n, m]) (Γ := Γβ) henv hΓβ ⟨uf, hfnHT⟩ hliftBodyC]
    exact hcLiftBodyC
  have hcLiftBodyB : safeTypeClass env Γr [n, m] liftBodyB = 0 ↔ m = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n, m]) (Γ := Γr) henv hΓr ⟨ub, hβHT⟩ hliftBodyF]
    exact hcLiftBodyF
  have hcLiftBodyR : safeTypeClass env Γα [n, m] liftBodyR = 0 ↔ m = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n, m]) (Γ := Γα) henv hΓα ⟨ur, hrelHT⟩ hliftBodyB]
    exact hcLiftBodyB
  have hliftc : env.HasType 2 [] liftc liftType := by
    simpa only [liftc, liftType, liftBodyR, liftBodyB, liftBodyF, liftBodyC,
      liftResult, liftQuot, α, respect, eqApp, rab, fn, β, rel, quotLiftConst,
      VExpr.instL, VLevel.inst, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ] using
      (VEnv.HasType.const (U := 2) (ls := [.param 0, .param 1])
        hLiftDecl (by decide) (by decide))
  have hliftType : env.IsType 2 [] liftType :=
    ⟨?_, by simp only [liftType, liftBodyR, liftBodyB, liftBodyF, liftBodyC,
      liftResult, liftQuot, α, respect, eqApp, rab, fn, β, rel]; type_tac⟩
  have hcLiftType : safeTypeClass env [] [n, m] liftType = 0 ↔ m = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n, m]) (Γ := []) henv trivial hα hliftBodyR]
    exact hcLiftBodyR
  have hcLiftc0 : safeTermClass env [] [n, m] liftc = 0 ↔ m = 0 :=
    safeTermClass_eq_zero_iff_of_typeClass (L := [n, m]) (Γ := []) henv trivial
      hliftc hliftType hcLiftType
  have hliftA0 : env.HasType 2 Γα liftA0 liftBodyR := by
    simp only [Γα, liftA0, liftc, liftBodyR, liftBodyB, liftBodyF, liftBodyC,
      liftResult, liftQuot, respect, eqApp, rab, fn, β, rel, α]; type_tac
  have hcLiftA0 : safeTermClass env Γα [n, m] liftA0 = 0 ↔ m = 0 :=
    safeTermClass_eq_zero_iff_of_typeClass (L := [n, m]) (Γ := Γα) henv hΓα
      hliftA0 hliftBodyR hcLiftBodyR
  have hliftR0 : env.HasType 2 Γr liftR0 liftBodyB := by
    simp only [Γr, liftR0, liftA0, liftc, liftBodyB, liftBodyF, liftBodyC,
      liftResult, liftQuot, respect, eqApp, rab, fn, β, rel, α]; type_tac
  have hcLiftR0 : safeTermClass env Γr [n, m] liftR0 = 0 ↔ m = 0 :=
    safeTermClass_eq_zero_iff_of_typeClass (L := [n, m]) (Γ := Γr) henv hΓr
      hliftR0 hliftBodyB hcLiftBodyB
  have hliftB0 : env.HasType 2 Γβ liftB0 liftBodyF := by
    simp only [Γβ, liftB0, liftR0, liftA0, liftc, liftBodyF, liftBodyC,
      liftResult, liftQuot, respect, eqApp, rab, fn, β, rel, α]; type_tac
  have hcLiftB0 : safeTermClass env Γβ [n, m] liftB0 = 0 ↔ m = 0 :=
    safeTermClass_eq_zero_iff_of_typeClass (L := [n, m]) (Γ := Γβ) henv hΓβ
      hliftB0 hliftBodyF hcLiftBodyF
  have hliftF0 : env.HasType 2 Γf liftF0 liftBodyC := by
    simp only [Γf, liftF0, liftB0, liftR0, liftA0, liftc, liftBodyC,
      liftResult, liftQuot, respect, eqApp, rab, fn, β, rel, α]; type_tac
  have hcLiftF0 : safeTermClass env Γf [n, m] liftF0 = 0 ↔ m = 0 :=
    safeTermClass_eq_zero_iff_of_typeClass (L := [n, m]) (Γ := Γf) henv hΓf
      hliftF0 hliftBodyC hcLiftBodyC
  have hliftC0 : env.HasType 2 Γc liftC0 liftResult := by
    simp only [Γc, liftC0, liftF0, liftB0, liftR0, liftA0, liftc, liftResult,
      liftQuot, respect, eqApp, rab, fn, β, rel, α]; type_tac
  have hcLiftC0 : safeTermClass env Γc [n, m] liftC0 = 0 ↔ m = 0 :=
    safeTermClass_eq_zero_iff_of_typeClass (L := [n, m]) (Γ := Γc) henv hΓc
      hliftC0 hliftResult hcLiftResult
  have hcLiftc : safeTermClass env Γa [n, m] liftc = 0 ↔ m = 0 := by
    have W : Ctx.LiftN 6 0 [] Γa := by
      simpa [Γa, Γc, Γf, Γβ, Γr, Γα] using Ctx.LiftN.zero
        ([.bvar 4, respect, fn, β, rel, α] : List VExpr)
    have hw := safeTermClass_weakN (L := [n, m]) (e := liftc) henv W
      (show OnCtx Γa (env.IsType 2) ↔ OnCtx [] (env.IsType 2) from
        ⟨fun _ => trivial, fun _ => hΓa⟩)
    simp only [liftc, VExpr.liftN] at hw
    rw [hw]
    exact hcLiftc0
  have hcLiftA : safeTermClass env Γa [n, m]
      ((VExpr.const ``Quot.lift [.param 0, .param 1]).app (.bvar 5)) = 0 ↔ m = 0 := by
    have W : Ctx.LiftN 5 0 Γα Γa := by
      simpa [Γa, Γα] using Ctx.LiftN.zero
        ([.bvar 4, respect, fn, β, rel] : List VExpr)
    have hw := safeTermClass_weakN (L := [n, m]) (e := liftA0) henv W
      (show OnCtx Γa (env.IsType 2) ↔ OnCtx Γα (env.IsType 2) from
        ⟨fun _ => hΓα, fun _ => hΓa⟩)
    simp [liftA0, liftc, VExpr.liftN, liftVar] at hw
    rw [hw]
    exact hcLiftA0
  have hcLiftR : safeTermClass env Γa [n, m]
      (((VExpr.const ``Quot.lift [.param 0, .param 1]).app (.bvar 5)).app
        (.bvar 4)) = 0 ↔ m = 0 := by
    have W : Ctx.LiftN 4 0 Γr Γa := by
      simpa [Γa, Γr] using Ctx.LiftN.zero
        ([.bvar 4, respect, fn, β] : List VExpr)
    have hw := safeTermClass_weakN (L := [n, m]) (e := liftR0) henv W
      (show OnCtx Γa (env.IsType 2) ↔ OnCtx Γr (env.IsType 2) from
        ⟨fun _ => hΓr, fun _ => hΓa⟩)
    simp [liftR0, liftA0, liftc, VExpr.lift, VExpr.liftN, liftVar] at hw
    rw [hw]
    exact hcLiftR0
  have hcLiftB : safeTermClass env Γa [n, m]
      ((((VExpr.const ``Quot.lift [.param 0, .param 1]).app (.bvar 5)).app
        (.bvar 4)).app (.bvar 3)) = 0 ↔ m = 0 := by
    have W : Ctx.LiftN 3 0 Γβ Γa := by
      simpa [Γa, Γβ] using Ctx.LiftN.zero ([.bvar 4, respect, fn] : List VExpr)
    have hw := safeTermClass_weakN (L := [n, m]) (e := liftB0) henv W
      (show OnCtx Γa (env.IsType 2) ↔ OnCtx Γβ (env.IsType 2) from
        ⟨fun _ => hΓβ, fun _ => hΓa⟩)
    simp [liftB0, liftR0, liftA0, liftc, VExpr.lift, VExpr.liftN, liftVar] at hw
    rw [hw]
    exact hcLiftB0
  have hcLiftF : safeTermClass env Γa [n, m]
      (((((VExpr.const ``Quot.lift [.param 0, .param 1]).app (.bvar 5)).app
        (.bvar 4)).app (.bvar 3)).app (.bvar 2)) = 0 ↔ m = 0 := by
    have W : Ctx.LiftN 2 0 Γf Γa := by
      simpa [Γa, Γf] using Ctx.LiftN.zero ([.bvar 4, respect] : List VExpr)
    have hw := safeTermClass_weakN (L := [n, m]) (e := liftF0) henv W
      (show OnCtx Γa (env.IsType 2) ↔ OnCtx Γf (env.IsType 2) from
        ⟨fun _ => hΓf, fun _ => hΓa⟩)
    simp [liftF0, liftB0, liftR0, liftA0, liftc, VExpr.lift,
      VExpr.liftN, liftVar] at hw
    rw [hw]
    exact hcLiftF0
  have hcLiftC : safeTermClass env Γa [n, m] liftApp = 0 ↔ m = 0 := by
    have W : Ctx.LiftN 1 0 Γc Γa := by
      simpa [Γa, Γc] using Ctx.LiftN.zero ([.bvar 4] : List VExpr)
    have hw := safeTermClass_weakN (L := [n, m]) (e := liftC0) henv W
      (show OnCtx Γa (env.IsType 2) ↔ OnCtx Γc (env.IsType 2) from
        ⟨fun _ => hΓc, fun _ => hΓa⟩)
    simp [liftC0, liftF0, liftB0, liftR0, liftA0, liftc,
      VExpr.lift, VExpr.liftN, liftVar] at hw
    rw [show liftApp = (((((VExpr.const ``Quot.lift [.param 0, .param 1]).app
      (.bvar 5)).app (.bvar 4)).app (.bvar 3)).app (.bvar 2)).app (.bvar 1) by
        rfl, hw]
    exact hcLiftC0
  let mkc : VExpr := .const ``Quot.mk [.param 0]
  let mkA : VExpr := mkc.app (.bvar 5)
  let mkR : VExpr := mkA.app (.bvar 4)
  let lmkR : VLevel := .imax (.param 0) (.param 0)
  let lmkA : VLevel := .imax lrel lmkR
  let lmkc : VLevel := .imax (.succ (.param 0)) lmkA
  have hmkc : env.HasType 2 Γa mkc quotMkConst.type := by
    simpa [mkc, quotMkConst, VExpr.instL, VLevel.inst] using
      (VEnv.HasType.const (U := 2) (Γ := Γa) (ls := [.param 0])
        hMkDecl (by decide) (by decide))
  have hmkcTy : env.HasType 2 Γa quotMkConst.type (.sort lmkc) := by
    simpa [quotMkConst, VExpr.instL, VLevel.inst] using (show env.HasType 2 Γa quotMkConst.type
        (.sort lmkc) from by
          simp only [quotMkConst, lmkc, lmkA, lmkR, lrel]
          apply VEnv.HasType.forallE
          · exact .sort (by decide)
          · apply VEnv.HasType.forallE
            · apply VEnv.HasType.forallE
              · type_tac
              · apply VEnv.HasType.forallE
                · type_tac
                · exact .sort trivial
            · apply VEnv.HasType.forallE
              · type_tac
              · apply VEnv.HasType.app'
                · type_tac
                · type_tac
                · rfl)
  have hcMkc : safeTermClass env Γa [n, m] mkc = 0 ↔ n = 0 := by
    rw [safeTermClass_eq_zero_iff_of_hasType (L := [n, m]) henv hΓa hmkc hmkcTy]
    simp [lmkc, lmkA, lmkR, lrel, VLevel.eval, Nat.imax]
  let mkAType : VExpr := .forallE
    (.forallE (.bvar 5) (.forallE (.bvar 6) (.sort .zero)))
    (.forallE (.bvar 6)
      (((VExpr.const ``Quot [.param 0]).app (.bvar 7)).app (.bvar 1)))
  have hmkA : env.HasType 2 Γa mkA mkAType := by
    simp only [Γa, mkA, mkAType, mkc, respect, eqApp, rab, fn, β, rel, α]
    type_tac
  have hmkATy : env.HasType 2 Γa mkAType (.sort lmkA) := by
    simp only [mkAType, lmkA, lmkR, lrel]
    apply VEnv.HasType.forallE
    · apply VEnv.HasType.forallE
      · type_tac
      · apply VEnv.HasType.forallE
        · type_tac
        · exact .sort trivial
    · apply VEnv.HasType.forallE
      · type_tac
      · apply VEnv.HasType.app'
        · type_tac
        · type_tac
        · rfl
  have hcMkA : safeTermClass env Γa [n, m] mkA = 0 ↔ n = 0 := by
    rw [safeTermClass_eq_zero_iff_of_hasType (L := [n, m]) henv hΓa hmkA hmkATy]
    simp [lmkA, lmkR, lrel, VLevel.eval, Nat.imax]
  let mkRType : VExpr := .forallE (.bvar 5)
    (((VExpr.const ``Quot [.param 0]).app (.bvar 6)).app (.bvar 5))
  have hmkR : env.HasType 2 Γa mkR mkRType := by
    simp only [Γa, mkR, mkRType, mkA, mkc, respect, eqApp, rab, fn, β, rel, α]
    type_tac
  have hmkRTy : env.HasType 2 Γa mkRType (.sort lmkR) := by
    simp only [mkRType, lmkR]
    apply VEnv.HasType.forallE
    · type_tac
    · apply VEnv.HasType.app'
      · type_tac
      · type_tac
      · rfl
  have hcMkR : safeTermClass env Γa [n, m] mkR = 0 ↔ n = 0 := by
    rw [safeTermClass_eq_zero_iff_of_hasType (L := [n, m]) henv hΓa hmkR hmkRTy]
    simp [lmkR, VLevel.eval, Nat.imax]
  let fnFinal : VExpr := fn.lift.lift.lift
  have hFFinal : env.HasType 2 Γa (.bvar 2) fnFinal := by
    simp only [Γa, fnFinal, respect, eqApp, rab, fn, β, rel, α]
    exact .bvar (by lookup_tac)
  have hFnFinalTy : env.HasType 2 Γa fnFinal (.sort lfn) := by
    simp only [fnFinal, fn, lfn]
    apply VEnv.HasType.forallE <;> type_tac
  have hcFFinal : safeTermClass env Γa [n, m] (.bvar 2) = 0 ↔ m = 0 := by
    rw [safeTermClass_eq_zero_iff_of_hasType (L := [n, m]) henv hΓa hFFinal hFnFinalTy]
    cases m <;> simp [lfn, VLevel.eval, Nat.imax]
  change interp κ env assignment [n, m] [] [] (.lam α lhsA) =
    interp κ env assignment [n, m] [] [] (.lam α rhsA)
  apply interp_lam_congr_of_hasType (L := [n, m]) (Γ := []) (γ := []) henv trivial
    hα
    (B := bodyR)
  · exact hlhsA
  · exact hrhsA
  · exact hbodyR
  · intro A hA
    apply interp_lam_congr_of_hasType (L := [n, m]) (Γ := Γα) (γ := [A])
      henv hΓα ⟨ur, hrelHT⟩ hlhsR hrhsR hbodyB
    intro r hr
    apply interp_lam_congr_of_hasType (L := [n, m]) (Γ := Γr) (γ := [r, A])
      henv hΓr ⟨ub, hβHT⟩ hlhsB hrhsB hbodyF
    intro B hB
    apply interp_lam_congr_of_hasType (L := [n, m]) (Γ := Γβ) (γ := [B, r, A])
      henv hΓβ ⟨uf, hfnHT⟩ hlhsF hrhsF hbodyC
    intro f hf
    apply interp_lam_congr_of_hasType (L := [n, m]) (Γ := Γf) (γ := [f, B, r, A])
      henv hΓf ⟨uc, hrespectHT⟩ hlhsC hrhsC hresult
    intro c hc
    apply interp_lam_congr_of_hasType (L := [n, m]) (Γ := Γc) (γ := [c, f, B, r, A])
      henv hΓc ⟨ua, haHT⟩ hlhsBody hrhsBody hres
    intro a ha
    have hA' : A ∈ ModelUniverse κ n := by
      simpa only [α, interp_sort, interpLevel, VLevel.eval, List.getD_cons_zero] using hA
    have hr' : r ∈ relationSpace A := by
      rw [← hrelation A]
      simpa only [Γα] using hr
    have hB' : B ∈ ModelUniverse κ m := by
      simpa only [Γr, β, interp_sort, interpLevel, VLevel.eval,
        List.getD_cons_zero, List.getD_cons_succ] using hB
    have hfnInterp :
        interp κ env assignment [n, m] Γβ [B, r, A] fn =
          piValue m A (fun _ => B) := by
      have hcFnCod' := hcFnCod
      simp only [β, rel, α] at hcFnCod'
      simp only [Γβ, fn, interp_forallE, interp_bvar,
        List.getD_cons_zero, List.getD_cons_succ]
      exact piValue_congr_zero hcFnCod' A (fun _ => B)
    have hf' : f ∈ piValue m A (fun _ => B) := by
      rw [← hfnInterp]
      exact hf
    have hc' : c ∈ quotLiftRespectValue assignment m A r B f := by
      rw [← hrespectInterp A r B f]
      simpa only [Γf] using hc
    have hrespect' : QuotientRespects m A (relationOfGraph r) f := by
      rw [quotRespectsType_eq hEq hr' hB' hf'] at hc'
      exact (mem_truthValue.1 hc').1
    have ha' : a ∈ A := by
      simpa only [Γc, interp_bvar, List.getD_cons_zero, List.getD_cons_succ] using ha
    change interp κ env assignment [n, m] Γa [a, c, f, B, r, A] lhsBody =
      interp κ env assignment [n, m] Γa [a, c, f, B, r, A] rhsBody
    have hcLiftc' := hcLiftc
    have hcLiftA' := hcLiftA
    have hcLiftR' := hcLiftR
    have hcLiftB' := hcLiftB
    have hcLiftF' := hcLiftF
    have hcLiftC' := hcLiftC
    have hcMkc' := hcMkc
    have hcMkA' := hcMkA
    have hcMkR' := hcMkR
    have hcFFinal' := hcFFinal
    simp only [liftc] at hcLiftc'
    simp only [mkc, mkA, mkR] at hcMkc' hcMkA' hcMkR'
    by_cases hm : m = 0
    · have hLiftC0 := hcLiftC'.2 hm
      have hF0 := hcFFinal'.2 hm
      simp only [lhsBody, rhsBody, interp_app, hLiftC0, hF0, appValue,
        if_pos, interp_bvar, List.getD_cons_zero, List.getD_cons_succ]
    · have hLiftcN : safeTermClass env Γa [n, m] liftc ≠ 0 :=
        fun h => hm (hcLiftc'.1 h)
      have hLiftAN := fun h => hm (hcLiftA'.1 h)
      have hLiftRN := fun h => hm (hcLiftR'.1 h)
      have hLiftBN := fun h => hm (hcLiftB'.1 h)
      have hLiftFN := fun h => hm (hcLiftF'.1 h)
      have hLiftCN := fun h => hm (hcLiftC'.1 h)
      have hFFinalN := fun h => hm (hcFFinal'.1 h)
      have hLiftConst : interp κ env assignment [n, m] Γa [a, c, f, B, r, A]
          liftc = quotLiftConstValue κ n m := by
        simp only [liftc, interp_const, hLiftcN, if_false, List.map,
          VLevel.eval, List.getD_cons_zero, List.getD_cons_succ, hQuot.2.1 n m]
      have hMkApp : interp κ env assignment [n, m] Γa [a, c, f, B, r, A]
          mkApp = quotMkValue n A (relationOfGraph r) a := by
        simp only [mkApp, interp_app, interp_bvar,
          List.getD_cons_zero, List.getD_cons_succ]
        rw [appValue_congr_zero hcMkR' _ _, appValue_congr_zero hcMkA' _ _,
          appValue_congr_zero hcMkc' _ _]
        by_cases hn : n = 0
        · simp [appValue, hn, quotMkValue_zero]
        · cases n with
          | zero => exact (hn rfl).elim
          | succ n =>
            have hMkcN : safeTermClass env Γa [n + 1, m]
                (VExpr.const ``Quot.mk [.param 0]) ≠ 0 :=
              fun h => Nat.succ_ne_zero n (hcMkc'.1 h)
            simp only [appValue, Nat.succ_ne_zero, if_false, interp_const,
              hMkcN, List.map, VLevel.eval, List.getD_cons_zero,
              hQuot.1.2 (n + 1), quotMkConstValue_succ, depApp_depLam hA',
              depApp_depLam hr', quotMkValue_succ]
            simpa [appValue, Nat.succ_ne_zero, quotMkValue_succ] using
              (app_quotMkFunction (n := n + 1) (A := A)
                (R := relationOfGraph r) ha')
      have hcCanon : c ∈ truthValue (QuotientRespects m A (relationOfGraph r) f) := by
        rw [← quotRespectsType_eq hEq hr' hB' hf']
        exact hc'
      have hLiftAppInterp :
          interp κ env assignment [n, m] Γa [a, c, f, B, r, A] liftApp =
            quotLiftFunction n m A (relationOfGraph r) f := by
        have hcLiftFraw := hcLiftF'
        have hcLiftBraw := hcLiftB'
        have hcLiftRraw := hcLiftR'
        have hcLiftAraw := hcLiftA'
        have hcLiftcraw := hcLiftc'
        simp only [liftApp, interp_app, interp_bvar, List.getD_cons_zero,
          List.getD_cons_succ]
        rw [appValue_congr_zero hcLiftFraw _ _, appValue_congr_zero hcLiftBraw _ _,
          appValue_congr_zero hcLiftRraw _ _, appValue_congr_zero hcLiftAraw _ _,
          appValue_congr_zero hcLiftcraw _ _]
        simp only [appValue, hm, if_false]
        rw [hLiftConst]
        simp only [quotLiftConstValue, lamValue, hm, if_false,
          depApp_depLam hA', depApp_depLam hr', depApp_depLam hB',
          depApp_depLam hf', depApp_depLam hcCanon]
      simp only [lhsBody, rhsBody, interp_app, interp_bvar,
        List.getD_cons_zero, hLiftAppInterp, hMkApp]
      rw [appValue_congr_zero hcLiftC' _ _, appValue_congr_zero hcFFinal' _ _]
      exact app_quotLiftFunction_mk_of_mem hA' hB' hf' hrespect' ha'

end Lean4LeanModel
