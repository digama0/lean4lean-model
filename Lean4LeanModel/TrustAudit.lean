import Lean4LeanModel.Consistency

/-!
# Trust-base audit

CI checks this command's output exactly. It records both the ordinary axioms used by the set model
and `sorryAx`, which currently comes from the three local declaration boundaries and explicitly
documented upstream proof debt.
-/

#print axioms Lean4LeanModel.consistency
