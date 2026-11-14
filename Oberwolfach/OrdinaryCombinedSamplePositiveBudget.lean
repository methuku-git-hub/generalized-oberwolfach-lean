module

public import Oberwolfach.OrdinaryReservoirErrorEventuallySmall

@[expose] public section
/-! Allocate the finite collection of sample-event failure probabilities
inside any positive margin left by the pre-existing event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach

theorem ordinary_combined_sample_positive_budget
    (lossE:ℝ) (hmargin:lossE<1):
    ∃χcap:ℝ,0<χcap ∧ ∃N:ℕ,1≤N ∧
    ∀n:ℕ,N≤n→∀χtwo χrows χdeep χcut χ χhost χref:ℝ,
    χtwo≤χcap→χrows≤χcap→χdeep≤χcap→χcut≤χcap→χ≤χcap→χhost≤χcap→χref≤χcap→
    0<1-((((lossE+χtwo)+χrows)+χdeep)+χcut)-2/(n:ℝ)^10-
      (1/(n:ℝ)+2/(n:ℝ)^2)-χ-χhost-χref :=by
  let χcap:ℝ:=(1-lossE)/16
  have hχ:0<χcap:=by dsimp [χcap];linarith
  have hm:lossE+7*χcap<1:=by dsimp [χcap];linarith
  obtain ⟨N,hN,hbound⟩:=ordinary_reservoir_error_eventually_small lossE (7*χcap) hm
  refine ⟨χcap,hχ,N,hN,?_⟩
  intro n hn χtwo χrows χdeep χcut χ χhost χref htwo hrows hdeep hcut hχ' hhost href
  have hn1:(1:ℝ)≤n:=by exact_mod_cast (show 1≤n by omega)
  have hn0:(0:ℝ)<n:=by linarith
  have hpow:(n:ℝ)≤(n:ℝ)^10:=by
    have hh:=pow_le_pow_right₀ hn1 (show (1:ℕ)≤10 by omega)
    simpa using hh
  have hinv:1/(n:ℝ)^10≤1/(n:ℝ):=one_div_le_one_div_of_le hn0 hpow
  have htwo':2/(n:ℝ)^10≤2/(n:ℝ):=by
    have h:=mul_le_mul_of_nonneg_left hinv (show (0:ℝ)≤2 by norm_num)
    simpa only [mul_one_div] using h
  have hh:=hbound n hn
  linarith only [hh,htwo',htwo,hrows,hdeep,hcut,hχ',hhost,href]
end Oberwolfach
