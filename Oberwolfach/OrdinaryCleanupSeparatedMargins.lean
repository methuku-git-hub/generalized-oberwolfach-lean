module

public import Oberwolfach.OrdinaryVortexCleanupUniformMargins

@[expose] public section
/-! Boundary extension tolerances can be chosen independently of the later
balance tolerance; only sampling and edit errors need follow that tolerance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_cleanup_separated_margins
    (K μ ν η b:ℝ) (hK:1≤K) (hμ:0<μ) (hν:0<ν) (hη:0<η) (hb:0≤b):
    let boundary:=min μ ν/(40*(K+1))
    let small:=min μ (min ν η)/(40*(K+1));
    0<boundary ∧ 0<small ∧ ∃M:ℕ,∀(A B parent:ℝ),
      (M:ℝ)≤A→(M:ℝ)≤B→0≤parent→parent≤K*A→parent≤K*B→B≤K*A→
      ∀(β εR εH βe βh cost p:ℝ),
      0≤β→β≤small→0≤εR→εR≤small→0≤εH→εH≤small→
      0≤βe→βe≤boundary→0≤βh→βh≤boundary→0≤cost→cost≤small*A→cost≤small*B→0≤p→p≤1→
      βe*parent+εR*A+3*(2*b+cost)≤μ*A ∧
      βh*parent+εH*B+2*(2*b+cost)≤ν*B ∧
      p*β*A+εR*A+2*(εH*B)+3*(2*b+cost)≤η*A:=by
  intro boundary small
  have hbound:0<boundary:=by dsimp [boundary];positivity
  have hsmall:0<small:=by dsimp [small];positivity
  have hbμ:boundary*(40*(K+1))≤μ:=by
    dsimp [boundary]
    rw [div_mul_cancel₀ _ (by positivity: (40*(K+1):ℝ)≠0)]
    exact min_le_left _ _
  have hbν:boundary*(40*(K+1))≤ν:=by
    dsimp [boundary]
    rw [div_mul_cancel₀ _ (by positivity: (40*(K+1):ℝ)≠0)]
    exact min_le_right _ _
  have hsμ:small*(40*(K+1))≤μ:=by
    dsimp [small]
    rw [div_mul_cancel₀ _ (by positivity: (40*(K+1):ℝ)≠0)]
    exact min_le_left _ _
  have hsν:small*(40*(K+1))≤ν:=by
    dsimp [small]
    rw [div_mul_cancel₀ _ (by positivity: (40*(K+1):ℝ)≠0)]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hsη:small*(40*(K+1))≤η:=by
    dsimp [small]
    rw [div_mul_cancel₀ _ (by positivity: (40*(K+1):ℝ)≠0)]
    exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨M,hM⟩:=exists_nat_gt (6*b/small)
  refine ⟨hbound,hsmall,M,?_⟩
  intro A B parent hA hB hp0 hpA hpB hBA β εR εH βe βh cost p
    hβ0 hβ hεR0 hεR hεH0 hεH hβe0 hβe hβh0 hβh hcost0 hcostA hcostB hp0' hp1
  have hA0:0≤A:=(Nat.cast_nonneg M).trans hA
  have hB0:0≤B:=(Nat.cast_nonneg M).trans hB
  have hconstA:6*b≤small*A:=by
    have hh:(6*b/small)≤A:=le_trans hM.le hA
    exact (div_le_iff₀ hsmall).mp hh |>.trans_eq (mul_comm A small)
  have hconstB:6*b≤small*B:=by
    have hh:(6*b/small)≤B:=le_trans hM.le hB
    exact (div_le_iff₀ hsmall).mp hh |>.trans_eq (mul_comm B small)
  have heA:βe*parent≤boundary*(K*A):=mul_le_mul hβe hpA hp0 hbound.le
  have heB:βh*parent≤boundary*(K*B):=mul_le_mul hβh hpB hp0 hbound.le
  have hr:εR*A≤small*A:=mul_le_mul_of_nonneg_right hεR hA0
  have hs:εH*B≤small*B:=mul_le_mul_of_nonneg_right hεH hB0
  have hsA:εH*B≤small*(K*A):=mul_le_mul hεH hBA hB0 hsmall.le
  have hbA:β*A≤small*A:=mul_le_mul_of_nonneg_right hβ hA0
  have hpβ:p*β*A≤β*A:=by nlinarith [mul_nonneg hβ0 hA0, mul_nonneg (sub_nonneg.mpr hp1) (mul_nonneg hβ0 hA0)]
  have h1:=mul_le_mul_of_nonneg_right hbμ hA0
  have h2:=mul_le_mul_of_nonneg_right hsμ hA0
  have h3:=mul_le_mul_of_nonneg_right hbν hB0
  have h4:=mul_le_mul_of_nonneg_right hsν hB0
  have h5:=mul_le_mul_of_nonneg_right hsη hA0
  have hKA:0≤(K-1)*small*A:=mul_nonneg (mul_nonneg (by linarith) hsmall.le) hA0
  have hKB:0≤(K-1)*small*B:=mul_nonneg (mul_nonneg (by linarith) hsmall.le) hB0
  have hbKA:0≤(K-1)*boundary*A:=mul_nonneg (mul_nonneg (by linarith) hbound.le) hA0
  have hbKB:0≤(K-1)*boundary*B:=mul_nonneg (mul_nonneg (by linarith) hbound.le) hB0
  have hsA0:0≤small*A:=mul_nonneg hsmall.le hA0
  have hsB0:0≤small*B:=mul_nonneg hsmall.le hB0
  have hbA0:0≤boundary*A:=mul_nonneg hbound.le hA0
  have hbB0:0≤boundary*B:=mul_nonneg hbound.le hB0
  constructor
  · nlinarith only [heA,hr,hconstA,hcostA,h1,h2,hKA,hbKA,hsA0,hbA0,hb]
  constructor
  · nlinarith only [heB,hs,hconstB,hcostB,h3,h4,hKB,hbKB,hsB0,hbB0,hb]
  · nlinarith only [hpβ,hbA,hr,hsA,hconstA,hcostA,h5,hKA,hsA0,hb]
end Oberwolfach
