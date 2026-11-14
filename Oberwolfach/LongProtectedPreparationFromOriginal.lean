module

public import Oberwolfach.LongProtectedPreparationFromOriginalTwoSplits

@[expose] public section
/-! Production name for the original-assumption long preparation. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem long_protected_preparation_from_original : LongProtectedPreparation :=
  long_protected_preparation_from_original_two_splits
end Oberwolfach
