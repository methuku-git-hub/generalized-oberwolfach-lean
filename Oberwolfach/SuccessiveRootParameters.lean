module

public import Oberwolfach.RootWheelCapParameters

@[expose] public section

/-! The cap and allowed number of roots are chosen before the forbidden
radius and the minimum neighbour-part size required by Hall's theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach

theorem successive_root_parameters (r:ℕ) (C β κ lam:ℝ)
    (hC:0≤C) (hβ:0<β) (hκ:0<κ) (hlam:0<lam) :
    ∃ K:ℕ,0<K ∧ ∃ θ:ℝ,0<θ ∧ ∀ d M:ℕ,∃ N:ℕ,∀ a m t:ℕ,
      N≤a → κ*a≤(m:ℝ) → (m:ℝ)≤C*a → (t:ℝ)≤θ*a →
      let L:ℝ:=t*max (2*(K+1)) r
      M≤m ∧ L≤lam*m ∧ L≤lam^2*m/16 ∧
        (m*r:ℕ)/(K:ℝ)+((r:ℝ)+3)*(d+1)+4*(K+1)+3*L<β*a := by
  obtain ⟨K,hK,ζ,hζ,N₀,hcap⟩:=root_wheel_cap_parameters r C (β/2) hC (by positivity)
  let D:ℝ:=(max (2*(K+1)) r:ℕ)
  have hD:0<D:=by
    dsimp [D]
    exact_mod_cast (show 0<max (2*(K+1)) r from lt_of_lt_of_le (by omega) (le_max_left _ _))
  let θ:=min (β/(12*D)) (min (lam*κ/D) (lam^2*κ/(16*D)))
  have hθ:0<θ:=by dsimp [θ];positivity
  refine ⟨K,hK,θ,hθ,?_⟩
  intro d M
  obtain ⟨N₁,hN₁⟩:=exists_nat_gt ((d:ℝ)/ζ)
  obtain ⟨N₂,hN₂⟩:=exists_nat_gt ((M:ℝ)/κ)
  refine ⟨max N₀ (max N₁ (max N₂ 1)),?_⟩
  intro a m t ha hmlo hmhi ht
  dsimp only
  have haR:(0:ℝ)<a:=Nat.cast_pos.mpr (by omega)
  have hd:(d:ℝ)≤ζ*a:=by
    have hh:=(div_lt_iff₀ hζ).mp (hN₁.trans_le (Nat.cast_le.mpr (show N₁≤a by omega)))
    nlinarith only [hh]
  have hM:M≤m:=by
    have hh:=(div_lt_iff₀ hκ).mp (hN₂.trans_le (Nat.cast_le.mpr (show N₂≤a by omega)))
    have hh':(M:ℝ)<m:=by nlinarith only [hh,hmlo]
    exact Nat.le_of_lt (Nat.cast_lt.mp hh')
  have htd:(t:ℝ)*D≤θ*a*D:=mul_le_mul_of_nonneg_right ht hD.le
  have hbθ:θ≤β/(12*D):=min_le_left _ _
  have hrθ:θ≤lam*κ/D:=(min_le_right _ _).trans (min_le_left _ _)
  have hcθ:θ≤lam^2*κ/(16*D):=(min_le_right _ _).trans (min_le_right _ _)
  have hbudgetL:(t:ℝ)*D≤β*a/12:=by
    have hh:=(le_div_iff₀ (by positivity:0<12*D)).mp hbθ
    have hh':=mul_le_mul_of_nonneg_right hh haR.le
    nlinarith only [htd,hh']
  have hrowL:(t:ℝ)*D≤lam*m:=by
    have hh:=(le_div_iff₀ hD).mp hrθ
    have hh':=mul_le_mul_of_nonneg_right hh haR.le
    have hm:=mul_le_mul_of_nonneg_left hmlo hlam.le
    nlinarith only [htd,hh',hm]
  have hcutL:(t:ℝ)*D≤lam^2*m/16:=by
    have hh:=(le_div_iff₀ (by positivity:0<16*D)).mp hcθ
    have hh':=mul_le_mul_of_nonneg_right hh haR.le
    have hm:=mul_le_mul_of_nonneg_left hmlo (sq_nonneg lam)
    nlinarith only [htd,hh',hm]
  have hc:=hcap a m (by omega) hmhi d (by positivity) hd
  refine ⟨hM,hrowL,hcutL,?_⟩
  change (m*r:ℕ)/(K:ℝ)+((r:ℝ)+3)*(d+1)+4*(K+1)+3*((t:ℝ)*D)<β*a
  nlinarith only [hc,hbudgetL,mul_pos hβ haR]

end Oberwolfach
