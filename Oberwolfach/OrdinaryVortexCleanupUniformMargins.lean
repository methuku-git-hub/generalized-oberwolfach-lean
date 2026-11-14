module

public import Oberwolfach.OrdinaryVortexProtectedTraceLocalBalance

@[expose] public section
/-! Once the geometric domain ratios and the latest trace loss are controlled,
one early choice of tolerances and terminal size supplies all three local
cleanup and balance margins, uniformly over later vortex levels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem ordinary_vortex_cleanup_uniform_margins
    (K μ ν η b:ℝ) (hK:1≤K) (hμ:0<μ) (hν:0<ν) (hη:0<η) (hb:0≤b):
    ∃δ:ℝ,0<δ ∧ ∃M:ℕ,∀(A B parent:ℝ),
      (M:ℝ)≤A→(M:ℝ)≤B→0≤parent→parent≤K*A→parent≤K*B→B≤K*A→
      ∀(β εR εH βe βh cost p:ℝ),
      0≤β→β≤δ→0≤εR→εR≤δ→0≤εH→εH≤δ→
      0≤βe→βe≤δ→0≤βh→βh≤δ→0≤cost→cost≤δ*A→cost≤δ*B→0≤p→p≤1→
      βe*parent+εR*A+3*(2*b+cost)≤μ*A ∧
      βh*parent+εH*B+2*(2*b+cost)≤ν*B ∧
      p*β*A+εR*A+2*(εH*B)+3*(2*b+cost)≤η*A:=by
  let δ:ℝ:=min μ (min ν η)/(10*(K+1))
  have hmin:0<min μ (min ν η):=lt_min hμ (lt_min hν hη)
  have hδ:0<δ:=by dsimp [δ]; positivity
  have hδμ:δ*(10*(K+1))≤μ:=by
    dsimp [δ]
    have hk:(10*(K+1):ℝ)≠0:=by positivity
    rw [div_mul_cancel₀ _ hk]
    exact min_le_left _ _
  have hδν:δ*(10*(K+1))≤ν:=by
    dsimp [δ]
    have hk:(10*(K+1):ℝ)≠0:=by positivity
    rw [div_mul_cancel₀ _ hk]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hδη:δ*(10*(K+1))≤η:=by
    dsimp [δ]
    have hk:(10*(K+1):ℝ)≠0:=by positivity
    rw [div_mul_cancel₀ _ hk]
    exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨M,hM⟩:=exists_nat_gt (6*b/δ)
  refine ⟨δ,hδ,M,?_⟩
  intro A B parent hA hB hp0 hpA hpB hBA β εR εH βe βh cost p
    hβ0 hβ hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh hcost0 hcostA hcostB hp0' hp1
  have hA0:0≤A:=(Nat.cast_nonneg M).trans hA
  have hB0:0≤B:=(Nat.cast_nonneg M).trans hB
  have hconstA:6*b≤δ*A:=by
    have hh:(6*b/δ)≤A:=le_trans hM.le hA
    exact (div_le_iff₀ hδ).mp hh |>.trans_eq (mul_comm A δ)
  have hconstB:6*b≤δ*B:=by
    have hh:(6*b/δ)≤B:=le_trans hM.le hB
    exact (div_le_iff₀ hδ).mp hh |>.trans_eq (mul_comm B δ)
  have heA:βe*parent≤δ*(K*A):=(mul_le_mul hβe hpA hp0 hδ.le)
  have heB:βh*parent≤δ*(K*B):=(mul_le_mul hβh hpB hp0 hδ.le)
  have hr:εR*A≤δ*A:=mul_le_mul_of_nonneg_right hεR hA0
  have hs:εH*B≤δ*B:=mul_le_mul_of_nonneg_right hεH hB0
  have hsA:εH*B≤δ*(K*A):=(mul_le_mul hεH hBA hB0 hδ.le)
  have hbA:β*A≤δ*A:=mul_le_mul_of_nonneg_right hβ hA0
  have hpβ:p*β*A≤β*A:=by nlinarith [mul_nonneg hβ0 hA0, mul_nonneg (sub_nonneg.mpr hp1) (mul_nonneg hβ0 hA0)]
  have hmA:=mul_le_mul_of_nonneg_right hδμ hA0
  have hnB:=mul_le_mul_of_nonneg_right hδν hB0
  have hhA:=mul_le_mul_of_nonneg_right hδη hA0
  constructor
  · nlinarith [mul_nonneg hδ.le hA0, mul_nonneg (sub_nonneg.mpr hK) (mul_nonneg hδ.le hA0)]
  constructor
  · nlinarith [mul_nonneg hδ.le hB0, mul_nonneg (sub_nonneg.mpr hK) (mul_nonneg hδ.le hB0)]
  · nlinarith [mul_nonneg hδ.le hA0, mul_nonneg (sub_nonneg.mpr hK) (mul_nonneg hδ.le hA0)]
end Oberwolfach
