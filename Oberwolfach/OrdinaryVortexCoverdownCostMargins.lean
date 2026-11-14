module

public import Oberwolfach.OrdinaryVortexCleanupUniformMargins

@[expose] public section
/-! The explicit root-first cover-down cost is small on both next domains
once its three rates are chosen early and the fixed completion cost is absorbed
by the terminal-size threshold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach

theorem ordinary_vortex_coverdown_cost_margins
    (K δ:ℝ) (hK:1≤K) (hδ:0<δ):
    ∃rate:ℝ,0<rate ∧ ∀C:ℝ,0≤C→∃M:ℕ,∀(A B parent ν η ρ:ℝ),
      (M:ℝ)≤A→(M:ℝ)≤B→0≤parent→parent≤K*A→parent≤K*B→
      0≤ν→ν≤rate*parent→0≤η→η≤rate*parent→0≤ρ→ρ≤rate→
      0≤ν+η+(2*(ρ*parent)+C) ∧
      ν+η+(2*(ρ*parent)+C)≤δ*A ∧
      ν+η+(2*(ρ*parent)+C)≤δ*B:=by
  let rate:ℝ:=δ/(8*K)
  have hk:0<K:=by linarith
  have hrate:0<rate:=by dsimp [rate];positivity
  have hrK:4*rate*K≤δ/2:=by
    dsimp [rate]
    field_simp
    norm_num
  refine ⟨rate,hrate,?_⟩
  intro C hC
  obtain ⟨M,hM⟩:=exists_nat_gt (2*C/δ)
  refine ⟨M,?_⟩
  intro A B parent ν η ρ hA hB hp0 hpA hpB hν0 hν hη0 hη hρ0 hρ
  have hA0:0≤A:=(Nat.cast_nonneg M).trans hA
  have hB0:0≤B:=(Nat.cast_nonneg M).trans hB
  have hCA:2*C≤δ*A:=by
    have hh:(2*C/δ)≤A:=hM.le.trans hA
    exact (div_le_iff₀ hδ).mp hh |>.trans_eq (mul_comm A δ)
  have hCB:2*C≤δ*B:=by
    have hh:(2*C/δ)≤B:=hM.le.trans hB
    exact (div_le_iff₀ hδ).mp hh |>.trans_eq (mul_comm B δ)
  have hρp:ρ*parent≤rate*parent:=mul_le_mul_of_nonneg_right hρ hp0
  have hrA:rate*parent≤rate*(K*A):=mul_le_mul_of_nonneg_left hpA hrate.le
  have hrB:rate*parent≤rate*(K*B):=mul_le_mul_of_nonneg_left hpB hrate.le
  have hrateA:=mul_le_mul_of_nonneg_right hrK hA0
  have hrateB:=mul_le_mul_of_nonneg_right hrK hB0
  constructor
  · positivity
  constructor
  · nlinarith only [hν,hη,hρp,hrA,hrateA,hCA]
  · nlinarith only [hν,hη,hρp,hrB,hrateB,hCB]
end Oberwolfach
