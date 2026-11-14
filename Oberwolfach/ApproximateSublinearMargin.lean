module

public import Oberwolfach.LongCapacityAutomaticMargins

@[expose] public section
/-! A fixed error margin eventually dominates the sublinear concentration
error together with the fixed separation loss. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section
open Filter
namespace Oberwolfach

theorem eventually_three_quarters_and_constant_le_linear (a B:ℝ) (ha:0<a):
    ∃N:ℕ,∀n≥N,(n:ℝ)^(3/4:ℝ)+B≤a*n:=by
  have ht:Filter.Tendsto (fun n:ℕ=>(n:ℝ)^((1:ℝ)/4)) Filter.atTop Filter.atTop:=
    (tendsto_rpow_atTop (y:=(1:ℝ)/4) (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀,hN₀⟩:=Filter.eventually_atTop.1 (ht.eventually (eventually_gt_atTop (2/a)))
  obtain ⟨N₁,hN₁⟩:=exists_nat_gt (2*B/a)
  refine ⟨max (max N₀ N₁) 1,?_⟩
  intro n hn
  have hn0:0<n:=by omega
  have hnR:(0:ℝ)<n:=by exact_mod_cast hn0
  have hroot:=hN₀ n (by omega)
  have hroot':2<a*(n:ℝ)^(1/4:ℝ):=by
    have hh:2<(n:ℝ)^(1/4:ℝ)*a:=(div_lt_iff₀ ha).1 hroot
    nlinarith
  have hpow:(n:ℝ)^(3/4:ℝ)*(n:ℝ)^(1/4:ℝ)=(n:ℝ):=by
    rw [←Real.rpow_add hnR]
    norm_num
  have hmul:=mul_nonneg (le_of_lt (sub_pos.mpr hroot')) (show 0≤(n:ℝ)^(3/4:ℝ) by positivity)
  have htbound:2*(n:ℝ)^(3/4:ℝ)≤a*n:=by nlinarith
  have hn1:(N₁:ℝ)≤n:=by exact_mod_cast (show N₁≤n by omega)
  have hB:2*B<a*n:=by
    have hh:2*B<(n:ℝ)*a:=(div_lt_iff₀ ha).1 (lt_of_lt_of_le hN₁ hn1)
    nlinarith
  linarith
end Oberwolfach
