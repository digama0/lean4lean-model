import Lean4LeanModel.Context
import Lean4Lean.Theory.Typing.EnvLemmas

/-!
# Global model data

The raw interpreter is total for every assignment, but soundness requires constants and primitive
definitional equations to receive values validating their declarations.  This module records that
global invariant separately from the per-context valuation relation.
-/

namespace Lean4LeanModel

open Lean4Lean

universe u

namespace Assignment

/-- An assignment validates every constant and primitive definitional equation in `env`. -/
structure WF (κ : ℕ → Cardinal.{u}) (env : VEnv) (assignment : Assignment.{u}) : Prop where
  const_mem : ∀ {c ci ns}, env.constants c = some ci → ns.length = ci.uvars →
    assignment.constVal c ns ∈ interp κ env assignment ns [] [] ci.type
  defeq : ∀ {df ns}, env.defeqs df → ns.length = df.uvars →
    interp κ env assignment ns [] [] df.lhs = interp κ env assignment ns [] [] df.rhs

end Assignment

/-- Global hypotheses shared by every semantic soundness statement. -/
structure ModelSetup (κ : ℕ → Cardinal.{u}) (env : VEnv) (assignment : Assignment.{u}) : Prop where
  cardinals_strictMono : StrictMono κ
  cardinals_inaccessible : ∀ n, (κ n).IsInaccessible
  environmentWF : env.WF
  assignmentWF : assignment.WF κ env

namespace ModelSetup

theorem envWF {κ : ℕ → Cardinal.{u}} {env : VEnv} {assignment : Assignment.{u}}
    (h : ModelSetup κ env assignment) : env.WF :=
  h.environmentWF

theorem envOrdered {κ : ℕ → Cardinal.{u}} {env : VEnv} {assignment : Assignment.{u}}
    (h : ModelSetup κ env assignment) : env.Ordered :=
  h.environmentWF.ordered

end ModelSetup

end Lean4LeanModel
