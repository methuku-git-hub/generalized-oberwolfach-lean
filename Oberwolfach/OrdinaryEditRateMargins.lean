module

public import Oberwolfach.OrdinaryTwoStagePackingMargins

@[expose] public section
/-! An edit rate chosen after the target margin absorbs the one forced root
edge for all sufficiently large orders and both domain sizes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach

theorem ordinary_edit_rate_and_forced_root (κ ω:ℝ) (hκ:0<κ) (hω:0<ω):
    ∃χ:ℝ,0<χ ∧ ∃N:ℕ,∀n m:ℕ,N≤n→ω*n≤m→∀d:ℝ,0≤d→d≤χ*n→
      d+1≤κ*n ∧ d≤κ*n ∧ d≤κ*m:=by
  let χ:=min (κ/4) (κ*ω/4)
  have hχ:0<χ:=by dsimp [χ];positivity
  have hχκ:χ≤κ/4:=min_le_left _ _
  have hχω:χ≤κ*ω/4:=min_le_right _ _
  obtain ⟨N,hN⟩:=exists_nat_gt (1/χ)
  refine ⟨χ,hχ,N,?_⟩
  intro n m hn hm d hd hdn
  have hnR:(N:ℝ)≤n:=Nat.cast_le.mpr hn
  have hlarge:1/χ≤(n:ℝ):=hN.le.trans hnR
  have hone:1≤χ*n:=by
    have hh:1≤(n:ℝ)*χ:=(div_le_iff₀ hχ).mp hlarge
    nlinarith only [hh]
  have hn0:(0:ℝ)≤n:=Nat.cast_nonneg _
  have hκn:=mul_le_mul_of_nonneg_right hχκ hn0
  have hωn:=mul_le_mul_of_nonneg_right hχω hn0
  have hκm:=mul_le_mul_of_nonneg_left hm hκ.le
  refine ⟨?_,?_,?_⟩ <;> nlinarith only [hdn,hone,hκn,hωn,hκm,hd]
end Oberwolfach
