module

public import Oberwolfach.OrdinaryReservoirErrorEventuallySmall

@[expose] public section
/-! Allocate a prescribed failure probability among the matching, reservoir,
parent, inner-weight and fine-cover events, retaining the requested n^-10 term. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach

theorem ordinary_common_sample_target_failure_budget
    (χ:ℝ) (hχ:0<χ):
    ∃cap:ℝ,0<cap ∧ ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→
    ∀lossE ζMatch χtwo χrows χdeep χcut χHub χEndpoint χhost χref χinner χfine:ℝ,
    lossE≤cap→ζMatch≤cap→χtwo≤cap→χrows≤cap→χdeep≤cap→χcut≤cap→
    χHub≤cap→χEndpoint≤cap→χhost≤cap→χref≤cap→χinner≤cap→χfine≤cap→
    lossE+ζMatch+χtwo+χrows+χdeep+χcut+χHub+χEndpoint+χhost+χref+χinner+χfine+
      2/(n:ℝ)^10+(1/(n:ℝ)+2/(n:ℝ)^2)≤χ+1/(n:ℝ)^10 :=by
  let cap:ℝ:=χ/24
  have hcap:0<cap:=by dsimp [cap];positivity
  obtain ⟨N,hN,hsmall⟩:=ordinary_reservoir_error_eventually_small (1-χ/2) 0 (by linarith)
  refine ⟨cap,hcap,N,hN,?_⟩
  intro n hn lossE ζMatch χtwo χrows χdeep χcut χHub χEndpoint χhost χref χinner χfine
    hE hMatch htwo hrows hdeep hcut hHub hEndpoint hhost href hinner hfine
  have hn1:(1:ℝ)≤n:=by exact_mod_cast (show 1≤n by omega)
  have hn0:(0:ℝ)<n:=by linarith
  have hpow:(n:ℝ)≤(n:ℝ)^10:=by
    have hh:=pow_le_pow_right₀ hn1 (show (1:ℕ)≤10 by omega)
    simpa using hh
  have hinv:1/(n:ℝ)^10≤1/(n:ℝ):=one_div_le_one_div_of_le hn0 hpow
  have hinv0:0≤1/(n:ℝ):=by positivity
  have htwo10:2/(n:ℝ)^10=2*(1/(n:ℝ)^10):=by ring
  have htwo1:2/(n:ℝ)=2*(1/(n:ℝ)):=by ring
  have hsmall':=hsmall n hn
  dsimp [cap] at hE hMatch htwo hrows hdeep hcut hHub hEndpoint hhost href hinner hfine
  linarith only [hE,hMatch,htwo,hrows,hdeep,hcut,hHub,hEndpoint,hhost,href,hinner,hfine,hinv,hinv0,htwo10,htwo1,hsmall']
end Oberwolfach
