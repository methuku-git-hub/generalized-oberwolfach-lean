module

public import Oberwolfach.OrdinaryChosenNaturalToPreparation
public import Oberwolfach.ConditionalPreparationMain

@[expose] public section
/-! Conditional theorem-level reduction: the chosen-reserve ordinary
probability and the long preparation proposition imply the main theorem. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_chosen_natural_probability_and_long_imply_main
    (hOrd:OrdinaryChosenNaturalPreparationProbability) (hLong:LongProtectedPreparation):MainTheorem :=by
  exact conditional_preparation_main (ordinary_chosen_natural_probability_implies_preparation hOrd) hLong
end Oberwolfach
