import Lean4LeanModel.ModelConstruction
import Lean4LeanModel.QuotientDefEqModel

/-!
# Installing quotient semantics

`VEnv.addQuot` is one declaration-history step containing four constants and one primitive
equation. Its intermediate environments are not themselves declaration histories, so the generic
one-constant extension theorem cannot be applied four times. This module provides the corresponding
bulk semantic extension theorem.
-/

namespace Lean4LeanModel

open Lean4Lean

universe u

private theorem addQuot_le' {env env' : VEnv}
    (hadd : env.addQuot = some env') : env ≤ env' := by
  unfold VEnv.addQuot at hadd
  rcases Option.bind_eq_some_iff.1 hadd with ⟨env₁, h₁, hadd⟩
  rcases Option.bind_eq_some_iff.1 hadd with ⟨env₂, h₂, hadd⟩
  rcases Option.bind_eq_some_iff.1 hadd with ⟨env₃, h₃, hadd⟩
  rcases Option.bind_eq_some_iff.1 hadd with ⟨env₄, h₄, hadd⟩
  simp only [Option.some.injEq] at hadd
  subst env'
  exact VEnv.LE.trans (VEnv.addConst_le h₁) (VEnv.LE.trans (VEnv.addConst_le h₂)
    (VEnv.LE.trans (VEnv.addConst_le h₃)
      (VEnv.LE.trans (VEnv.addConst_le h₄) VEnv.addDefEq_le)))

/-- Semantic data for the completed `addQuot` environment. Keeping this interface in terms of the
five generated objects makes it independent of how canonical equality is eventually obtained from
the inductive construction. -/
structure QuotientMeanings (κ : ℕ → Cardinal.{u}) (env : VEnv)
    (assignment : Assignment.{u})
    (quot quotMk quotLift quotInd : List Nat → ZFSet.{u}) : Prop where
  quot_valid : ∀ ns, ns.length = quotConst.uvars →
    quot ns ∈ interp κ env assignment ns [] [] quotConst.type
  quotMk_valid : ∀ ns, ns.length = quotMkConst.uvars →
    quotMk ns ∈ interp κ env assignment ns [] [] quotMkConst.type
  quotLift_valid : ∀ ns, ns.length = quotLiftConst.uvars →
    quotLift ns ∈ interp κ env assignment ns [] [] quotLiftConst.type
  quotInd_valid : ∀ ns, ns.length = quotIndConst.uvars →
    quotInd ns ∈ interp κ env assignment ns [] [] quotIndConst.type
  quotDefEq_valid : ∀ ns, ns.length = quotDefEq.uvars →
    interp κ env assignment ns [] [] quotDefEq.lhs =
      interp κ env assignment ns [] [] quotDefEq.rhs

noncomputable def canonicalQuotMeaning (κ : ℕ → Cardinal.{u})
    (ns : List Nat) : ZFSet.{u} := quotTypeValue κ (ns.getD 0 0)

noncomputable def canonicalQuotMkMeaning (κ : ℕ → Cardinal.{u})
    (ns : List Nat) : ZFSet.{u} := quotMkConstValue κ (ns.getD 0 0)

noncomputable def canonicalQuotLiftMeaning (κ : ℕ → Cardinal.{u})
    (ns : List Nat) : ZFSet.{u} :=
  quotLiftConstValue κ (ns.getD 0 0) (ns.getD 1 0)

noncomputable def canonicalQuotIndMeaning (_κ : ℕ → Cardinal.{u})
    (_ns : List Nat) : ZFSet.{u} := quotIndConstValue

noncomputable def Assignment.withCanonicalQuotients (κ : ℕ → Cardinal.{u})
    (assignment : Assignment.{u}) : Assignment.{u} :=
  ((((assignment.set ``Quot (canonicalQuotMeaning κ)).set ``Quot.mk
    (canonicalQuotMkMeaning κ)).set ``Quot.lift (canonicalQuotLiftMeaning κ)).set
    ``Quot.ind (canonicalQuotIndMeaning κ))

theorem Assignment.withCanonicalQuotients_modelsQuotPrimitives
    {κ : ℕ → Cardinal.{u}} (assignment : Assignment.{u}) :
    (assignment.withCanonicalQuotients κ).ModelsQuotPrimitives κ := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro n
    simp [Assignment.withCanonicalQuotients, Assignment.set, canonicalQuotMeaning]
  · intro n
    simp [Assignment.withCanonicalQuotients, Assignment.set, canonicalQuotMkMeaning]
  · intro n m
    simp [Assignment.withCanonicalQuotients, Assignment.set, canonicalQuotLiftMeaning]
  · intro n
    simp [Assignment.withCanonicalQuotients, Assignment.set, canonicalQuotIndMeaning]

/-- Package the exact declaration and computation-rule bridges for the canonical quotient
assignment. This is the narrow proof interface between the set construction and the bulk
environment extension. -/
theorem canonicalQuotientMeanings {κ : ℕ → Cardinal.{u}} {env : VEnv}
    {assignment : Assignment.{u}} (henv : env.WF)
    (hi : ∀ n, (κ n).IsInaccessible)
    (hEqDecl : env.constants ``Eq = some eqConst)
    (hQuotDecl : env.constants ``Quot = some quotConst)
    (hMkDecl : env.constants ``Quot.mk = some quotMkConst)
    (hLiftDecl : env.constants ``Quot.lift = some quotLiftConst)
    (hEq : (assignment.withCanonicalQuotients κ).ModelsEq κ) :
    QuotientMeanings κ env (assignment.withCanonicalQuotients κ)
      (canonicalQuotMeaning κ) (canonicalQuotMkMeaning κ)
      (canonicalQuotLiftMeaning κ) (canonicalQuotIndMeaning κ) := by
  constructor
  · intro ns hns
    obtain ⟨n, rfl⟩ := List.length_eq_one_iff.1 hns
    simpa [canonicalQuotMeaning] using quotConstValue_valid (assignment :=
      assignment.withCanonicalQuotients κ) henv hi n
  · intro ns hns
    obtain ⟨n, rfl⟩ := List.length_eq_one_iff.1 hns
    apply quotMkConstValue_valid henv hQuotDecl
    · intro k
      simp [Assignment.withCanonicalQuotients, Assignment.set, canonicalQuotMeaning]
  · intro ns hns
    change ns.length = 2 at hns
    rcases ns with _ | ⟨n, ns⟩
    · simp at hns
    · rcases ns with _ | ⟨m, ns⟩
      · simp at hns
      · rcases ns with _ | ⟨k, ns⟩
        · simpa [canonicalQuotLiftMeaning] using quotLiftConstValue_valid henv hEqDecl
            hQuotDecl hEq
            (Assignment.withCanonicalQuotients_modelsQuotPrimitives assignment).1.1 n m
        · simp at hns
  · intro ns hns
    obtain ⟨n, rfl⟩ := List.length_eq_one_iff.1 hns
    simpa [canonicalQuotIndMeaning] using quotIndConstValue_valid henv hQuotDecl
      hMkDecl (Assignment.withCanonicalQuotients_modelsQuotPrimitives assignment).1 n
  · intro ns hns
    change ns.length = 2 at hns
    rcases ns with _ | ⟨n, ns⟩
    · simp at hns
    · rcases ns with _ | ⟨m, ns⟩
      · simp at hns
      · rcases ns with _ | ⟨k, ns⟩
        · exact quotDefEq_valid henv hEqDecl hQuotDecl hMkDecl hLiftDecl hEq
            (Assignment.withCanonicalQuotients_modelsQuotPrimitives assignment) n m
        · simp at hns

/-- Install all four quotient meanings and their beta rule in one semantic environment step. -/
theorem model_addQuot_sem {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment : Assignment.{u}} (M : ModelSetup κ env assignment)
    (hadd : env.addQuot = some env') (henv' : env'.WF)
    (quot quotMk quotLift quotInd : List Nat → ZFSet.{u})
    (meanings : QuotientMeanings κ env'
      ((((assignment.set ``Quot quot).set ``Quot.mk quotMk).set
        ``Quot.lift quotLift).set ``Quot.ind quotInd) quot quotMk quotLift quotInd) :
    ModelSetup κ env'
      ((((assignment.set ``Quot quot).set ``Quot.mk quotMk).set
        ``Quot.lift quotLift).set ``Quot.ind quotInd) := by
  unfold VEnv.addQuot at hadd
  rcases Option.bind_eq_some_iff.1 hadd with ⟨env₁, h₁, hadd⟩
  rcases Option.bind_eq_some_iff.1 hadd with ⟨env₂, h₂, hadd⟩
  rcases Option.bind_eq_some_iff.1 hadd with ⟨env₃, h₃, hadd⟩
  rcases Option.bind_eq_some_iff.1 hadd with ⟨env₄, h₄, hadd⟩
  simp only [Option.some.injEq] at hadd
  subst env'
  let assignment₁ := assignment.set ``Quot quot
  let assignment₂ := assignment₁.set ``Quot.mk quotMk
  let assignment₃ := assignment₂.set ``Quot.lift quotLift
  let assignment₄ := assignment₃.set ``Quot.ind quotInd
  have hle₁ := VEnv.addConst_le h₁
  have hle₂ := VEnv.addConst_le h₂
  have hle₃ := VEnv.addConst_le h₃
  have hle₄ := VEnv.addConst_le h₄
  have hle : env ≤ env₄.addDefEq quotDefEq := by
    exact VEnv.LE.trans hle₁ (VEnv.LE.trans hle₂
      (VEnv.LE.trans hle₃ (VEnv.LE.trans hle₄ VEnv.addDefEq_le)))
  have hfresh₁ := addConst_fresh h₁
  have hfresh₂ := addConst_fresh h₂
  have hfresh₃ := addConst_fresh h₃
  have hfresh₄ := addConst_fresh h₄
  have hext : Assignment.Extends env assignment assignment₄ := by
    intro c ci hc ns
    have hc₁ : c ≠ ``Quot := by
      intro h
      subst c
      rw [hfresh₁] at hc
      contradiction
    have hc₂ : c ≠ ``Quot.mk := by
      intro h
      subst c
      have := hle₁.constants hc
      rw [hfresh₂] at this
      contradiction
    have hc₃ : c ≠ ``Quot.lift := by
      intro h
      subst c
      have := hle₂.constants (hle₁.constants hc)
      rw [hfresh₃] at this
      contradiction
    have hc₄ : c ≠ ``Quot.ind := by
      intro h
      subst c
      have := hle₃.constants (hle₂.constants (hle₁.constants hc))
      rw [hfresh₄] at this
      contradiction
    simp [assignment₄, assignment₃, assignment₂, assignment₁, Assignment.set,
      hc₁, hc₂, hc₃, hc₄]
  change ModelSetup κ (env₄.addDefEq quotDefEq) assignment₄
  refine ⟨M.cardinals_strictMono, M.cardinals_inaccessible, henv', ?_⟩
  constructor
  · intro c ci ns hc hns
    change env₄.constants c = some ci at hc
    rcases addConst_lookup_cases h₄ hc with hnew | hc
    · rcases hnew with ⟨rfl, rfl⟩
      simpa [assignment₄] using meanings.quotInd_valid ns hns
    rcases addConst_lookup_cases h₃ hc with hnew | hc
    · rcases hnew with ⟨rfl, rfl⟩
      simpa [assignment₄, assignment₃, assignment₂, assignment₁, Assignment.set_self,
        Assignment.set_other _ _ (by decide : (`Quot.lift : Name) ≠ `Quot.ind)] using
        meanings.quotLift_valid ns hns
    rcases addConst_lookup_cases h₂ hc with hnew | hc
    · rcases hnew with ⟨rfl, rfl⟩
      simpa [assignment₄, assignment₃, assignment₂, assignment₁, Assignment.set_self,
        Assignment.set_other _ _ (by decide : (`Quot.mk : Name) ≠ `Quot.ind),
        Assignment.set_other _ _ (by decide : (`Quot.mk : Name) ≠ `Quot.lift)] using
        meanings.quotMk_valid ns hns
    rcases addConst_lookup_cases h₁ hc with hnew | hc
    · rcases hnew with ⟨rfl, rfl⟩
      simpa [assignment₄, assignment₃, assignment₂, assignment₁, Assignment.set_self,
        Assignment.set_other _ _ (by decide : (`Quot : Name) ≠ `Quot.ind),
        Assignment.set_other _ _ (by decide : (`Quot : Name) ≠ `Quot.lift),
        Assignment.set_other _ _ (by decide : (`Quot : Name) ≠ `Quot.mk)] using
        meanings.quot_valid ns hns
    · have hOld := M.assignmentWF.const_mem hc hns
      obtain ⟨lvl, hci⟩ := M.envOrdered.constWF hc
      have hciWF : ci.type.WF env ci.uvars [] := ⟨.sort lvl, hci⟩
      have htypeExt := interp_extension (κ := κ) hle M.envWF henv' hext
        (L := ns) (Γ := []) (γ := []) trivial ci.type (by simpa [hns] using hciWF)
      rw [hext hc ns]
      exact htypeExt.symm ▸ hOld
  · intro df ns hdf hns
    change df = quotDefEq ∨ env₄.defeqs df at hdf
    rcases hdf with rfl | hdf
    · exact meanings.quotDefEq_valid ns hns
    · have hdfOld : env.defeqs df := by
        exact addConst_defeq_old h₁
          (addConst_defeq_old h₂ (addConst_defeq_old h₃ (addConst_defeq_old h₄ hdf)))
      have hOld := M.assignmentWF.defeq hdfOld hns
      obtain ⟨hl, hr⟩ := M.envOrdered.defEqWF hdfOld
      have hlExt := interp_extension (κ := κ) hle M.envWF henv' hext
        (L := ns) (Γ := []) (γ := []) trivial df.lhs (by
          simpa [hns] using show df.lhs.WF env df.uvars [] from ⟨df.type, hl⟩)
      have hrExt := interp_extension (κ := κ) hle M.envWF henv' hext
        (L := ns) (Γ := []) (γ := []) trivial df.rhs (by
          simpa [hns] using show df.rhs.WF env df.uvars [] from ⟨df.type, hr⟩)
      exact hlExt.trans (hOld.trans hrExt.symm)

/-- Complete the `addQuot` model step using the canonical quotient assignment, preserving the
canonical meanings of both `Eq` and the four quotient primitives. The only semantic premise beyond
the existing model is the canonical meaning of `Eq`. -/
theorem model_addQuot_canonical {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment : Assignment.{u}} (M : ModelSetup κ env assignment)
    (hready : env.QuotReady) (hadd : env.addQuot = some env') (henv' : env'.WF)
    (hEq : assignment.ModelsEq κ) :
    ModelSetup κ env' (assignment.withCanonicalQuotients κ) ∧
      (assignment.withCanonicalQuotients κ).ModelsEq κ ∧
      (assignment.withCanonicalQuotients κ).ModelsQuotPrimitives κ := by
  have hEqDecl : env'.constants ``Eq = some eqConst := (addQuot_le' hadd).constants hready
  have hEq' : (assignment.withCanonicalQuotients κ).ModelsEq κ := hEq.congr (by
    intro ns
    simp [Assignment.withCanonicalQuotients, Assignment.set])
  refine ⟨?_, hEq', Assignment.withCanonicalQuotients_modelsQuotPrimitives assignment⟩
  apply model_addQuot_sem M hadd henv'
    (canonicalQuotMeaning κ) (canonicalQuotMkMeaning κ)
    (canonicalQuotLiftMeaning κ) (canonicalQuotIndMeaning κ)
  exact canonicalQuotientMeanings henv' M.cardinals_inaccessible hEqDecl
    (VEnv.addQuot_quot hadd) (VEnv.addQuot_quotMk hadd)
    (VEnv.addQuot_quotLift hadd) hEq'

end Lean4LeanModel
