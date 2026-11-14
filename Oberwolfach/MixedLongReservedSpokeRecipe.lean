module

public import Oberwolfach.MixedMarkedReservedMatchingEvent
public import Oberwolfach.MixedAssignedSamplingRecipes

@[expose] public section
/-! In the marked class the ordinary reservation colour has fixed density
1/100, independently of the factor and of the interval length. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {I:Type} {U:I→Type} [∀i,Fintype (U i)] {n:ℕ}

theorem mixed_long_reserved_spoke_recipe
    (K m:ℕ) (s θ:ℝ) (label:I→Option (Fin K))
    (F:∀i,U i→SimpleGraph (Fin n)) (hF:∀i w,(F i w).IsRegularOfDegree 2)
    (i:I) (hi:label i=none) (w:U i):
    mixedAssignedSpokeProbability K m s θ label F hF i w false=1/100:=by
  simp [mixedAssignedSpokeProbability,hi,longAssignedSpokeProbability]
end Oberwolfach
