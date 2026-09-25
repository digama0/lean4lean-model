import Lean4LeanModel.Consistency
import Lean4LeanModel.QuotientConstruction

/-!
# Trust-base audit

CI checks these commands' output exactly. They record both the headline theorem's trust base and
the quotient declaration bridges. `sorryAx` remains visible where generated typing facts depend on
the explicitly documented upstream proof debt.
-/

#print axioms Lean4LeanModel.consistency
#print axioms Lean4LeanModel.quotConstValue_valid
#print axioms Lean4LeanModel.quotMkConstValue_valid
#print axioms Lean4LeanModel.quotRespectsType_eq
#print axioms Lean4LeanModel.quotLiftConstValue_valid
#print axioms Lean4LeanModel.quotIndConstValue_valid
#print axioms Lean4LeanModel.quotDefEq_valid
#print axioms Lean4LeanModel.model_addQuot_canonical
