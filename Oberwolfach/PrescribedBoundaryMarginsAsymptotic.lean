module

public import Oberwolfach.ApproximateSublinearMargin

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem prescribed_boundary_margins_eventually
    (δ:ℝ) (hδ:0<δ):
    ∃d₀ N:ℕ,1≤d₀ ∧ 1≤N ∧ ∀d≥d₀, ∀n≥N,
      4/(d:ℝ)≤δ/8 ∧ 4*(n:ℝ)^(3/4:ℝ)≤δ*n/8:=by
  obtain ⟨d₀,hd₀⟩:=exists_nat_gt (32/δ)
  obtain ⟨N,hN⟩:=eventually_three_quarters_and_constant_le_linear (δ/32) 0 (by positivity)
  refine ⟨max d₀ 1,max N 1,le_max_right _ _,le_max_right _ _,?_⟩
  intro d hd n hn
  have hd':(32/δ)<(d:ℝ):=lt_of_lt_of_le hd₀ (by exact_mod_cast (le_trans (le_max_left d₀ 1) hd))
  have hdpos:(0:ℝ)<d:=by exact_mod_cast (show 0<d by omega)
  have hmul:(32:ℝ)<(d:ℝ)*δ:=(div_lt_iff₀ hδ).1 hd'
  have hfirst:4/(d:ℝ)≤δ/8:=by
    apply (div_le_iff₀ hdpos).2
    nlinarith only [hmul]
  have hn':N≤n:=le_trans (le_max_left N 1) hn
  have hh:=hN n hn'
  constructor
  · exact hfirst
  · linarith only [hh]
end Oberwolfach
