module

public import Oberwolfach.MarkedExpandedPhysicalLaw

@[expose] public section
/-! The grouped sampled class has exactly the sum of the first five physical
state probabilities. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem expanded_physical_class_mass (p k p₂ k₂ u:ℝ):
    (∑a∈({0,1,2,3,4}:Finset (Fin 6)),markedExpandedPhysicalProbability p k p₂ k₂ u a)=
      2*p+2*k+2*p₂+2*k₂+u:=by
  norm_num [markedExpandedPhysicalProbability]
  ring
end Oberwolfach
