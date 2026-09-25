import Lean4LeanModel.SetQuotient
import Lean4LeanModel.DependentFunction

/-!
# Proof-irrelevant semantic quotients

`setQuotient` is the ordinary set quotient used in positive universes. At universe level zero the
quotient is a proposition, so its representation is collapsed to a truth value just like every
other proposition in the model.
-/

namespace Lean4LeanModel

universe u

/-- The semantic type of binary proposition-valued relations on `A`. -/
noncomputable def relationSpace (A : ZFSet.{u}) : ZFSet.{u} :=
  depFuns A fun _ => depFuns A fun _ => propUniverse

/-- Read a metatheoretic relation from a semantic function graph. -/
noncomputable def relationOfGraph (r : ZFSet.{u}) (a b : ZFSet.{u}) : Prop :=
  bullet ∈ depApp (depApp r a) b

theorem relationOfGraph_mem_prop {A r a b : ZFSet.{u}}
    (hr : r ∈ relationSpace A) (ha : a ∈ A) (hb : b ∈ A) :
    depApp (depApp r a) b ∈ propUniverse := by
  have hra : depApp r a ∈ depFuns A (fun _ => propUniverse) :=
    depApp_mem (mem_depFuns.1 hr) ha
  exact depApp_mem (mem_depFuns.1 hra) hb

/-- Semantic quotient type, dispatched between proof-irrelevant `Prop` and set-valued data. -/
noncomputable def quotValue (n : Nat) (A : ZFSet.{u})
    (R : ZFSet.{u} → ZFSet.{u} → Prop) : ZFSet.{u} :=
  if n = 0 then truthValue (∃ a, a ∈ A) else setQuotient A R

/-- Semantic quotient constructor. Proofs are collapsed to `bullet`; data is sent to its class. -/
noncomputable def quotMkValue (n : Nat) (A : ZFSet.{u})
    (R : ZFSet.{u} → ZFSet.{u} → Prop) (a : ZFSet.{u}) : ZFSet.{u} :=
  if n = 0 then bullet else setQuotClass A R a

@[simp]
theorem quotValue_zero (A : ZFSet.{u}) (R : ZFSet.{u} → ZFSet.{u} → Prop) :
    quotValue 0 A R = truthValue (∃ a, a ∈ A) := by
  simp [quotValue]

@[simp]
theorem quotValue_succ (n : Nat) (A : ZFSet.{u}) (R : ZFSet.{u} → ZFSet.{u} → Prop) :
    quotValue (n + 1) A R = setQuotient A R := by
  simp [quotValue]

@[simp]
theorem quotMkValue_zero (A : ZFSet.{u}) (R : ZFSet.{u} → ZFSet.{u} → Prop)
    (a : ZFSet.{u}) : quotMkValue 0 A R a = bullet := by
  simp [quotMkValue]

@[simp]
theorem quotMkValue_succ (n : Nat) (A : ZFSet.{u})
    (R : ZFSet.{u} → ZFSet.{u} → Prop) (a : ZFSet.{u}) :
    quotMkValue (n + 1) A R a = setQuotClass A R a := by
  simp [quotMkValue]

/-- Every quotient value is represented by an element of the source. -/
theorem mem_quotValue_iff {n : Nat} {A : ZFSet.{u}}
    {R : ZFSet.{u} → ZFSet.{u} → Prop} {q : ZFSet.{u}} :
    q ∈ quotValue n A R ↔ ∃ a ∈ A, quotMkValue n A R a = q := by
  cases n with
  | zero =>
      simp only [quotValue_zero, mem_truthValue, quotMkValue_zero]
      constructor
      · rintro ⟨⟨a, ha⟩, rfl⟩
        exact ⟨a, ha, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, rfl⟩
  | succ n => simp

theorem quotMkValue_mem {n : Nat} {A : ZFSet.{u}}
    {R : ZFSet.{u} → ZFSet.{u} → Prop} {a : ZFSet.{u}} (ha : a ∈ A) :
    quotMkValue n A R a ∈ quotValue n A R :=
  mem_quotValue_iff.2 ⟨a, ha, rfl⟩

/-- `Quot.sound` at the semantic-operation level. -/
theorem quotMkValue_sound {n : Nat} {A : ZFSet.{u}}
    {R : ZFSet.{u} → ZFSet.{u} → Prop} {a b : ZFSet.{u}}
    (ha : a ∈ A) (hb : b ∈ A) (hab : R a b) :
    quotMkValue n A R a = quotMkValue n A R b := by
  cases n with
  | zero => simp
  | succ n => simpa using setQuot_sound ha hb hab

/-- The modeled quotient constructor after its type and relation arguments have been supplied. -/
noncomputable def quotMkFunction (n : Nat) (A : ZFSet.{u})
    (R : ZFSet.{u} → ZFSet.{u} → Prop) : ZFSet.{u} :=
  lamValue n A (quotMkValue n A R)

theorem quotMkFunction_mem {n : Nat} {A : ZFSet.{u}}
    {R : ZFSet.{u} → ZFSet.{u} → Prop} :
    quotMkFunction n A R ∈ piValue n A (fun _ => quotValue n A R) := by
  apply lamValue_mem_piValue
  · intro a ha
    exact quotMkValue_mem ha
  · intro hn _ _
    simpa [hn] using truthValue_mem_propUniverse (∃ a, a ∈ A)

theorem app_quotMkFunction {n : Nat} {A : ZFSet.{u}}
    {R : ZFSet.{u} → ZFSet.{u} → Prop} {a : ZFSet.{u}} (ha : a ∈ A) :
    appValue n (quotMkFunction n A R) a = quotMkValue n A R a := by
  apply appValue_lamValue
  · intro b hb
    exact quotMkValue_mem hb
  · intro hn _ _
    simpa [hn] using truthValue_mem_propUniverse (∃ a, a ∈ A)
  · exact ha

/-- Evaluate a function on a quotient representative. The default is unreachable on members of
`quotValue`. -/
noncomputable def quotLiftValue (n : Nat) (A : ZFSet.{u})
    (R : ZFSet.{u} → ZFSet.{u} → Prop) (f : ZFSet.{u} → ZFSet.{u})
    (q : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if h : ∃ a ∈ A, quotMkValue n A R a = q then f (Classical.choose h) else ∅

/-- A relation-respecting function is constant on semantic quotient representatives. At level
zero this additionally uses proof irrelevance of the source proposition. -/
theorem eq_of_quotMkValue_eq {n : Nat} {A : ZFSet.{u}}
    {R : ZFSet.{u} → ZFSet.{u} → Prop} {f : ZFSet.{u} → ZFSet.{u}}
    (hA : n = 0 → A ∈ (propUniverse : ZFSet.{u}))
    (hf : ∀ a ∈ A, ∀ b ∈ A, R a b → f a = f b)
    {a b : ZFSet.{u}} (ha : a ∈ A) (hb : b ∈ A)
    (hab : quotMkValue n A R a = quotMkValue n A R b) : f a = f b := by
  cases n with
  | zero =>
      have ha' := eq_bullet_of_mem_prop (hA rfl) ha
      have hb' := eq_bullet_of_mem_prop (hA rfl) hb
      exact congrArg f (ha'.trans hb'.symm)
  | succ n =>
      exact eq_of_setQuotEqv hf ((setQuotClass_eq_iff hb).1 (by simpa using hab))

theorem quotLiftValue_mk {n : Nat} {A : ZFSet.{u}}
    {R : ZFSet.{u} → ZFSet.{u} → Prop} {f : ZFSet.{u} → ZFSet.{u}}
    (hA : n = 0 → A ∈ (propUniverse : ZFSet.{u}))
    (hf : ∀ a ∈ A, ∀ b ∈ A, R a b → f a = f b)
    {a : ZFSet.{u}} (ha : a ∈ A) :
    quotLiftValue n A R f (quotMkValue n A R a) = f a := by
  classical
  have hrep : ∃ b ∈ A, quotMkValue n A R b = quotMkValue n A R a := ⟨a, ha, rfl⟩
  simp only [quotLiftValue, dif_pos hrep]
  have hb := (Classical.choose_spec hrep).1
  have heq := (Classical.choose_spec hrep).2
  exact eq_of_quotMkValue_eq hA hf hb ha heq

theorem quotLiftValue_mem {n : Nat} {A : ZFSet.{u}}
    {R : ZFSet.{u} → ZFSet.{u} → Prop} {f : ZFSet.{u} → ZFSet.{u}}
    (hA : n = 0 → A ∈ (propUniverse : ZFSet.{u}))
    (hf : ∀ a ∈ A, ∀ b ∈ A, R a b → f a = f b)
    {B q : ZFSet.{u}} (hfB : ∀ a ∈ A, f a ∈ B) (hq : q ∈ quotValue n A R) :
    quotLiftValue n A R f q ∈ B := by
  obtain ⟨a, ha, rfl⟩ := mem_quotValue_iff.1 hq
  rw [quotLiftValue_mk hA hf ha]
  exact hfB a ha

/-- The modeled quotient lift after its source, relation, target, function, and respect proof have
been supplied. -/
noncomputable def quotLiftFunction (n m : Nat) (A : ZFSet.{u})
    (R : ZFSet.{u} → ZFSet.{u} → Prop) (f : ZFSet.{u}) : ZFSet.{u} :=
  lamValue m (quotValue n A R) (quotLiftValue n A R (appValue m f))

theorem quotLiftFunction_mem {n m : Nat} {A B : ZFSet.{u}}
    {R : ZFSet.{u} → ZFSet.{u} → Prop} {f : ZFSet.{u}}
    (hA : n = 0 → A ∈ (propUniverse : ZFSet.{u}))
    (hf : f ∈ piValue m A (fun _ => B))
    (hrespect : ∀ a ∈ A, ∀ b ∈ A, R a b → appValue m f a = appValue m f b)
    (hB : m = 0 → B ∈ (propUniverse : ZFSet.{u})) :
    quotLiftFunction n m A R f ∈ piValue m (quotValue n A R) (fun _ => B) := by
  apply lamValue_mem_piValue
  · intro q hq
    apply quotLiftValue_mem hA hrespect (fun a ha => appValue_mem hf ha) hq
  · intro hm _ _
    exact hB hm

theorem app_quotLiftFunction_mk {n m : Nat} {A B : ZFSet.{u}}
    {R : ZFSet.{u} → ZFSet.{u} → Prop} {f : ZFSet.{u}}
    (hA : n = 0 → A ∈ (propUniverse : ZFSet.{u}))
    (hf : f ∈ piValue m A (fun _ => B))
    (hrespect : ∀ a ∈ A, ∀ b ∈ A, R a b → appValue m f a = appValue m f b)
    (hB : m = 0 → B ∈ (propUniverse : ZFSet.{u}))
    {a : ZFSet.{u}} (ha : a ∈ A) :
    appValue m (quotLiftFunction n m A R f) (quotMkValue n A R a) = appValue m f a := by
  unfold quotLiftFunction
  rw [appValue_lamValue
    (fun q hq => quotLiftValue_mem hA hrespect (fun x hx => appValue_mem hf hx) hq)
    (fun hm _ _ => hB hm) (quotMkValue_mem ha)]
  exact quotLiftValue_mk hA hrespect ha

/-- Semantic quotient induction: every quotient element is the image of a source element. -/
theorem quotValue_ind {n : Nat} {A : ZFSet.{u}}
    {R : ZFSet.{u} → ZFSet.{u} → Prop} {P : ZFSet.{u} → Prop}
    (hP : ∀ a ∈ A, P (quotMkValue n A R a))
    {q : ZFSet.{u}} (hq : q ∈ quotValue n A R) : P q := by
  obtain ⟨a, ha, rfl⟩ := mem_quotValue_iff.1 hq
  exact hP a ha

/-- Proof-irrelevant semantic form of `Quot.ind`. -/
theorem bullet_mem_quotInd {n : Nat} {A : ZFSet.{u}}
    {R : ZFSet.{u} → ZFSet.{u} → Prop} {P : ZFSet.{u} → ZFSet.{u}}
    (hP : ∀ a ∈ A, bullet ∈ P (quotMkValue n A R a)) :
    bullet ∈ forallValue (quotValue n A R) P := by
  rw [bullet_mem_forallValue]
  intro q hq
  exact quotValue_ind (P := fun q => bullet ∈ P q) hP hq

theorem quotValue_mem_ModelUniverse {κ : ℕ → Cardinal.{u}}
    (hi : ∀ n, (κ n).IsInaccessible) {n : Nat} {A : ZFSet.{u}}
    {R : ZFSet.{u} → ZFSet.{u} → Prop} (hA : A ∈ ModelUniverse κ n) :
    quotValue n A R ∈ ModelUniverse κ n := by
  cases n with
  | zero => exact truthValue_mem_propUniverse _
  | succ n =>
      change SmallAt (κ n) (setQuotient A R)
      exact smallAt_setQuotient (hi n) hA

/-- Semantic value of the quotient type former at universe level `n`. -/
noncomputable def quotTypeValue (κ : ℕ → Cardinal.{u}) (n : Nat) : ZFSet.{u} :=
  depLam (ModelUniverse κ n) fun A =>
    depLam (relationSpace A) fun r => quotValue n A (relationOfGraph r)

/-- The quotient type former inhabits its expected nested function space. -/
theorem quotTypeValue_mem {κ : ℕ → Cardinal.{u}}
    (hi : ∀ n, (κ n).IsInaccessible) (n : Nat) :
    quotTypeValue κ n ∈ depFuns (ModelUniverse κ n) (fun A =>
      depFuns (relationSpace A) (fun _ => ModelUniverse κ n)) := by
  apply depLam_mem_depFuns
  intro A hA
  apply depLam_mem_depFuns
  intro r _
  exact quotValue_mem_ModelUniverse hi hA

/-- Semantic value of `Quot.mk` at universe level `n`. -/
noncomputable def quotMkConstValue (κ : ℕ → Cardinal.{u}) (n : Nat) : ZFSet.{u} :=
  lamValue n (ModelUniverse κ n) fun A =>
    lamValue n (relationSpace A) fun r => quotMkFunction n A (relationOfGraph r)

@[simp] theorem quotMkConstValue_zero (κ : ℕ → Cardinal.{u}) :
    quotMkConstValue κ 0 = bullet := by
  simp [quotMkConstValue, lamValue]

@[simp] theorem quotMkConstValue_succ (κ : ℕ → Cardinal.{u}) (n : Nat) :
    quotMkConstValue κ (n + 1) =
      depLam (ModelUniverse κ (n + 1)) fun A =>
        depLam (relationSpace A) fun r =>
          quotMkFunction (n + 1) A (relationOfGraph r) := by
  simp [quotMkConstValue, lamValue]

private theorem piValue_mem_propUniverse_of_zero {m : Nat} (hm : m = 0)
    (A : ZFSet.{u}) (B : ZFSet.{u} → ZFSet.{u}) :
    piValue m A B ∈ (propUniverse : ZFSet.{u}) := by
  subst m
  exact forallValue_mem_propUniverse A B

theorem quotMkConstValue_mem {κ : ℕ → Cardinal.{u}} (n : Nat) :
    quotMkConstValue κ n ∈ piValue n (ModelUniverse κ n) (fun A =>
      piValue n (relationSpace A) (fun r =>
        piValue n A (fun _ => quotValue n A (relationOfGraph r)))) := by
  apply lamValue_mem_piValue
  · intro A _
    apply lamValue_mem_piValue
    · intro r _
      exact quotMkFunction_mem
    · intro hn _ _
      exact piValue_mem_propUniverse_of_zero hn _ _
  · intro hn _ _
    exact piValue_mem_propUniverse_of_zero hn _ _

/-- The metatheoretic proposition asserted by the respect argument of `Quot.lift`. -/
def QuotientRespects (m : Nat) (A : ZFSet.{u})
    (R : ZFSet.{u} → ZFSet.{u} → Prop) (f : ZFSet.{u}) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, R a b → appValue m f a = appValue m f b

/-- Semantic value of `Quot.lift` at source level `n` and target level `m`, with equality in its
respect argument exposed as metatheoretic equality. `QuotientModel` states the canonical `Eq`
invariant and proves the implication needed to obtain this proposition. -/
noncomputable def quotLiftConstValue (κ : ℕ → Cardinal.{u}) (n m : Nat) : ZFSet.{u} :=
  lamValue m (ModelUniverse κ n) fun A =>
    lamValue m (relationSpace A) fun r =>
      lamValue m (ModelUniverse κ m) fun B =>
        lamValue m (piValue m A (fun _ => B)) fun f =>
          lamValue m (truthValue (QuotientRespects m A (relationOfGraph r) f)) fun _ =>
            quotLiftFunction n m A (relationOfGraph r) f

theorem quotLiftConstValue_mem {κ : ℕ → Cardinal.{u}} (n m : Nat) :
    quotLiftConstValue κ n m ∈ piValue m (ModelUniverse κ n) (fun A =>
      piValue m (relationSpace A) (fun r =>
        piValue m (ModelUniverse κ m) (fun B =>
          piValue m (piValue m A (fun _ => B)) (fun f =>
            piValue m (truthValue (QuotientRespects m A (relationOfGraph r) f)) (fun _ =>
              piValue m (quotValue n A (relationOfGraph r)) (fun _ => B)))))) := by
  apply lamValue_mem_piValue
  · intro A hA
    apply lamValue_mem_piValue
    · intro r hr
      apply lamValue_mem_piValue
      · intro B hB
        apply lamValue_mem_piValue
        · intro f hf
          apply lamValue_mem_piValue
          · intro _ hrespect
            apply quotLiftFunction_mem
            · intro hn
              simpa [hn] using hA
            · exact hf
            · exact (mem_truthValue.1 hrespect).1
            · intro hm
              simpa [hm] using hB
          · intro hm _ _
            exact piValue_mem_propUniverse_of_zero hm _ _
        · intro hm _ _
          exact piValue_mem_propUniverse_of_zero hm _ _
      · intro hm _ _
        exact piValue_mem_propUniverse_of_zero hm _ _
    · intro hm _ _
      exact piValue_mem_propUniverse_of_zero hm _ _
  · intro hm _ _
    exact piValue_mem_propUniverse_of_zero hm _ _

/-- The semantic computation rule after all arguments of the quotient lift have been supplied. -/
theorem app_quotLiftFunction_mk_of_mem {κ : ℕ → Cardinal.{u}} {n m : Nat}
    {A B r f : ZFSet.{u}}
    (hA : A ∈ ModelUniverse κ n) (hB : B ∈ ModelUniverse κ m)
    (hf : f ∈ piValue m A (fun _ => B))
    (hrespect : QuotientRespects m A (relationOfGraph r) f)
    {a : ZFSet.{u}} (ha : a ∈ A) :
    appValue m (quotLiftFunction n m A (relationOfGraph r) f)
      (quotMkValue n A (relationOfGraph r) a) = appValue m f a := by
  apply app_quotLiftFunction_mk
  · intro hn
    simpa [hn] using hA
  · exact hf
  · exact hrespect
  · intro hm
    simpa [hm] using hB
  · exact ha

/-- The semantic proposition expressing the premise of quotient induction. -/
noncomputable def quotIndPremise (n : Nat) (A : ZFSet.{u})
    (R : ZFSet.{u} → ZFSet.{u} → Prop) (P : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  forallValue A fun a => P (quotMkValue n A R a)

theorem bullet_mem_quotInd_of_premise {n : Nat} {A : ZFSet.{u}}
    {R : ZFSet.{u} → ZFSet.{u} → Prop} {P : ZFSet.{u} → ZFSet.{u}}
    (h : bullet ∈ quotIndPremise n A R P) :
    bullet ∈ forallValue (quotValue n A R) P := by
  apply bullet_mem_quotInd
  exact bullet_mem_forallValue.1 h

/-- Semantic predicates on a quotient. Predicates themselves are data-valued function graphs,
while each fiber is a proof-irrelevant proposition. -/
noncomputable def quotPredicateSpace (n : Nat) (A : ZFSet.{u})
    (R : ZFSet.{u} → ZFSet.{u} → Prop) : ZFSet.{u} :=
  depFuns (quotValue n A R) fun _ => propUniverse

/-- The semantic type of `Quot.ind` at universe level `n`. -/
noncomputable def quotIndTypeValue (κ : ℕ → Cardinal.{u}) (n : Nat) : ZFSet.{u} :=
  forallValue (ModelUniverse κ n) fun A =>
    forallValue (relationSpace A) fun r =>
      forallValue (quotPredicateSpace n A (relationOfGraph r)) fun P =>
        forallValue (quotIndPremise n A (relationOfGraph r) (depApp P)) fun _ =>
          forallValue (quotValue n A (relationOfGraph r)) (depApp P)

/-- Proof-irrelevant semantic value of the quotient induction primitive. -/
noncomputable def quotIndConstValue : ZFSet.{u} := bullet

theorem quotIndConstValue_mem {κ : ℕ → Cardinal.{u}} (n : Nat) :
    quotIndConstValue ∈ quotIndTypeValue κ n := by
  simp only [quotIndConstValue, quotIndTypeValue, bullet_mem_forallValue]
  intro A _ r _ P _ c hprem
  have hc : c = bullet := eq_bullet_of_mem_prop
    (forallValue_mem_propUniverse A fun a => depApp P (quotMkValue n A (relationOfGraph r) a))
    hprem
  exact bullet_mem_forallValue.1 (bullet_mem_quotInd_of_premise (hc ▸ hprem))

theorem quotLiftValue_smallAt {c : Cardinal.{u}} {n : Nat} {A : ZFSet.{u}}
    {R : ZFSet.{u} → ZFSet.{u} → Prop} {f : ZFSet.{u} → ZFSet.{u}}
    (hA : n = 0 → A ∈ (propUniverse : ZFSet.{u}))
    (hf : ∀ a ∈ A, ∀ b ∈ A, R a b → f a = f b)
    {q : ZFSet.{u}} (hq : q ∈ quotValue n A R)
    (hsmall : ∀ a ∈ A, SmallAt c (f a)) : SmallAt c (quotLiftValue n A R f q) := by
  obtain ⟨a, ha, rfl⟩ := mem_quotValue_iff.1 hq
  rw [quotLiftValue_mk hA hf ha]
  exact hsmall a ha

end Lean4LeanModel
