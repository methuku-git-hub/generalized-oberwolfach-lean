module

public import Oberwolfach.OrdinaryNaturalToPreparation
public import Oberwolfach.ConditionalPreparationMain

@[expose] public section
/-! The main theorem follows once the ordinary natural same-sample
certificate bound and the long preparation proposition are proved. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_natural_and_long_preparation_imply_main
    (hOrd:OrdinaryNaturalPreparationProbability) (hLong:LongProtectedPreparation):MainTheorem :=
  conditional_preparation_main (ordinary_natural_probability_implies_preparation hOrd) hLong
end Oberwolfach
