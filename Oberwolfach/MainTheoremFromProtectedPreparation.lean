module

public import Oberwolfach.LongPreparationImpliesMain
public import Oberwolfach.LongProtectedPreparationFromOriginal

@[expose] public section

/-! Final wrappers for the original fixed-set and uniform target propositions. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem fixedSetTheoremProof : FixedSetTheorem :=
  long_preparation_implies_fixed_set long_protected_preparation_from_original

theorem mainTheoremProof : MainTheorem :=
  long_preparation_implies_main long_protected_preparation_from_original

end Oberwolfach
