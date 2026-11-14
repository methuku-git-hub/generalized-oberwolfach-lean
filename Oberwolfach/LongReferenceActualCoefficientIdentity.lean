module

public import Oberwolfach.LongAssignedReferenceRecipeIdentity

@[expose] public section
/-! The ordinary rim target uses the supplied frequency coefficient; it is
not replaced by a uniform coefficient after sampling. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem long_reference_rim_coefficient_identity {U I:Type} [Fintype U]
    (θ:ℝ) (f:I→U→ℝ) (b:U→ℝ) (η:I→U→ℝ)
    (hb:∀u,0<b u) (hη:∀i u,η i u=(1-θ)*f i u/b u):
    ∀i,∑u,η i u*b u=(1-θ)*∑u,f i u :=by
  intro i
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [hη i u]
  field_simp [(hb u).ne']
end Oberwolfach
