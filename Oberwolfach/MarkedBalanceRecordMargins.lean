module

public import Oberwolfach.MarkedReferenceLevelData

@[expose] public section
/-! Explicit tolerances fitting the inner and global balance margins. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach

theorem marked_balance_record_margin_choice (c:ℕ) (η x:ℝ) (hη:0<η) (hx:0<x):
    ∃ eps ζ:ℝ,0<eps ∧ 0<ζ ∧
      eps+(c+2:ℕ)*ζ≤η ∧ eps+(c+2:ℕ)*ζ≤x/2:=by
  let θ:=min η (x/2)
  have hθ:0<θ:=by dsimp [θ];positivity
  have hc:0<(c+2:ℕ):=by omega
  have hc':(0:ℝ)<(c+2:ℕ):=by exact_mod_cast hc
  have hsum:θ/4+(c+2:ℕ)*(θ/(4*(c+2:ℕ)))=θ/2:=by
    field_simp
    <;> ring
  refine ⟨θ/4,θ/(4*(c+2:ℕ)),by positivity,by positivity,?_,?_⟩
  · rw [hsum]
    have hh:θ≤η:=min_le_left _ _
    linarith
  · rw [hsum]
    have hh:θ≤x/2:=min_le_right _ _
    linarith

theorem marked_balance_record_error_bounds
    (η x eps ζ:ℝ) (c:ℕ) (a b n:ℝ)
    (hx0:0≤x) (ha:0≤a) (hb:0≤b) (han:a≤n) (hbn:b≤n)
    (hη:eps+(c+2:ℕ)*ζ≤η) (hx:eps+(c+2:ℕ)*ζ≤x/2):
    (eps+(c+2:ℕ)*ζ)*a≤η*a ∧
    (eps+(c+2:ℕ)*ζ)*a≤(x/2)*n ∧
    (eps+(c+2:ℕ)*ζ)*b≤(x/2)*n:=by
  constructor
  · exact mul_le_mul_of_nonneg_right hη ha
  constructor
  · nlinarith [mul_nonneg hx0 (sub_nonneg.mpr han),mul_nonneg ha (sub_nonneg.mpr hx)]
  · nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hbn),mul_nonneg hb (sub_nonneg.mpr hx)]
end Oberwolfach
