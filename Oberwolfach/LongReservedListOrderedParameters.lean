module

public import Oberwolfach.LongOrientationDeletionReserve

@[expose] public section
/-! Choose the independent reserved-list coefficient before the remainder
fraction and the minimum reference length. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_reserved_list_ordered_parameters
    (αHost ρ₀:ℝ) (hα:0<αHost) (hρ:0<ρ₀):
    ∃β βE:ℝ,∃M:ℕ,
      β=(min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16 ∧ βE=β/2 ∧
      0<β ∧ 0<βE ∧ 1≤M ∧ ∀m≥M,∃θ:ℝ,
        0<θ ∧ θ≤1/100 ∧ 10*θ≤(βE/100)^2 ∧ 1/(100*(m:ℝ))≤βE/8 := by
  let β:ℝ:=(min αHost (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16
  have hβ:0<β:=by dsimp [β];positivity
  let βE:ℝ:=β/2
  have hβE:0<βE:=by dsimp [βE];positivity
  let θ:ℝ:=min (1/100:ℝ) ((βE/100)^2/20)/2
  have hθ:0<θ:=by dsimp [θ]; positivity
  obtain ⟨k,hk⟩:=exists_nat_gt (1/(100*(βE/8)))
  refine ⟨β,βE,max 1 (k+1),rfl,rfl,hβ,hβE,by omega,?_⟩
  intro m hm
  refine ⟨θ,hθ,?_,?_,?_⟩
  · dsimp [θ]
    have hh:=min_le_left (1/100:ℝ) ((βE/100)^2/20)
    linarith
  · dsimp [θ]
    have hh:=min_le_right (1/100:ℝ) ((βE/100)^2/20)
    nlinarith [sq_nonneg (βE/100)]
  · have hmpos:0<(m:ℝ):=by exact_mod_cast (show 0<m by omega)
    have hkm:(k:ℝ)≤m:=by exact_mod_cast (show k≤m by omega)
    have hmgt:1/(100*(βE/8))<(m:ℝ):=hk.trans_le hkm
    have hmul:1<(m:ℝ)*(100*(βE/8)):=
      (div_lt_iff₀ (by positivity :0<100*(βE/8))).mp hmgt
    apply (div_le_iff₀ (by positivity :0<100*(m:ℝ))).2
    nlinarith
end Oberwolfach
