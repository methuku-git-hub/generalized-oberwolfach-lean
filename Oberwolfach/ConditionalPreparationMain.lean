module

public import Oberwolfach.ConditionalPreparationFixedSet
public import Oberwolfach.UniformGrid

@[expose] public section
/-! Both manuscript preparation propositions together imply the original
uniform main theorem. Their proofs are not supplied by this reduction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem conditional_preparation_main
    (hOrd:OrdinaryProtectedPreparation) (hLong:LongProtectedPreparation):MainTheorem :=
  uniform_of_fixed_set_grid (conditional_preparation_fixed_set hOrd hLong)
end Oberwolfach
