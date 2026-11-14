module

public import Oberwolfach.LongOrientationDeletionReserve

@[expose] public section
/-! A previously chosen common vortex error can be used in the reserved-list
budget, provided it obeys the cap fixed before that choice. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_shared_error_reserved_list_budget
    (β εQ ηcap ζcap:ℝ) (m:ℕ) (hβ:0<β) (hε:0≤εQ) (hεcap:εQ≤β/32)
    (hη:0<ηcap) (hζ:0<ζcap) (hm:1/(100*(m:ℝ))≤β/16):
    ∃lam η ζ:ℝ,0<lam ∧ 0<η ∧ η≤ηcap ∧ 0<ζ ∧ ζ≤ζcap ∧
      β/2+εQ+1/(100*(m:ℝ))+η≤lam ∧ lam+2*ζ≤β ∧
      ∀n:ℕ,(lam+2*ζ)*n≤β*n := by
  refine ⟨3*β/4,min ηcap (β/32),min ζcap (β/16),by positivity,by positivity,
    min_le_left _ _,by positivity,min_le_left _ _,?_,?_,?_⟩
  · have hh:=min_le_right ηcap (β/32)
    linarith
  · have hz:=min_le_right ζcap (β/16)
    linarith
  · intro n
    have hz:=min_le_right ζcap (β/16)
    have hbound:3*β/4+2*min ζcap (β/16)≤β:=by linarith
    exact mul_le_mul_of_nonneg_right hbound (by positivity)
end Oberwolfach
