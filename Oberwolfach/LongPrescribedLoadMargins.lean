module

public import Oberwolfach.LongSelectedListMargins

@[expose] public section
/-! For any positive load tolerance, choose the path parameter and ambient
order so that the sampled interval contribution fits the load budget. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach

theorem long_prescribed_load_margins (δ:ℝ) (hδ:0<δ):
    ∃mMin:ℕ,∀m:ℕ,mMin≤m→4/(m:ℝ)≤δ/4 ∧
      ∃N:ℕ,∀n:ℕ,N≤n→4*(n:ℝ)^(3/4:ℝ)≤δ*n/4:=by
  obtain ⟨M,hM⟩:=exists_nat_gt (16/δ)
  refine ⟨max M 1,?_⟩
  intro m hm
  have hm0:0<(m:ℝ):=by exact_mod_cast (show 0<m by omega)
  have hm':16/δ≤(m:ℝ):=le_of_lt (lt_of_lt_of_le hM (by exact_mod_cast (show M≤m by omega)))
  have hsmall:4/(m:ℝ)≤δ/4:=by
    have hh:16≤(m:ℝ)*δ:=(div_le_iff₀ hδ).1 hm'
    apply (div_le_iff₀ hm0).2
    nlinarith
  refine ⟨hsmall,?_⟩
  obtain ⟨N,hN⟩:=eventually_three_quarters_and_constant_le_linear (δ/16) 0 (by positivity)
  refine ⟨N,?_⟩
  intro n hn
  have hh:=hN n hn
  nlinarith
end Oberwolfach
