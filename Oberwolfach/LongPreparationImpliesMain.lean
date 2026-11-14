module

public import Oberwolfach.OrdinaryProtectedPreparationFromOriginal
public import Oberwolfach.ConditionalPreparationMain

@[expose] public section
/-! The original ordinary preparation is available; the remaining protected
long preparation implies the fixed-set and main theorems. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_preparation_implies_fixed_set (hLong:LongProtectedPreparation):FixedSetTheorem :=
  conditional_preparation_fixed_set ordinary_protected_preparation_from_original hLong

theorem long_preparation_implies_main (hLong:LongProtectedPreparation):MainTheorem :=
  conditional_preparation_main ordinary_protected_preparation_from_original hLong
end Oberwolfach
