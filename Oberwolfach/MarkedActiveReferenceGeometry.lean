module

public import Oberwolfach.MarkedActiveReferenceScale

@[expose] public section

/-! Order and deletion inequalities for the same active row and hub sets.
All losses are measured against the original row order. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace Oberwolfach

theorem marked_active_reference_geometry_from_scale
    (n m nA mA omega kappa delta:ℝ)
    (hn:0<n) (ho:0<omega) (ho1:omega≤1) (hk:0≤kappa)
    (hk4:kappa≤1/4) (hkO:kappa≤omega/2) (hd:0≤delta)
    (hkD:kappa≤delta*omega/2)
    (hR:n-nA≤kappa*n) (hU:m-mA≤kappa*n) (hubs:omega*n≤m):
    (3/4:ℝ)*n≤nA∧n/2≤nA∧omega*n/2≤mA∧0<nA∧0<mA∧
    (1-delta/2)*n≤nA∧(1-delta/2)*m≤mA∧
    kappa*n≤(2*kappa/omega)*nA∧kappa*n≤(2*kappa/omega)*mA:=by
  have hn0:=hn.le
  have hn4:=mul_le_mul_of_nonneg_right hk4 hn0
  have hnO:=mul_le_mul_of_nonneg_right hkO hn0
  have hA:(3/4:ℝ)*n≤nA:=by linarith only [hR,hn4]
  have hAhalf:n/2≤nA:=by linarith only [hA,hn]
  have hB:omega*n/2≤mA:=by linarith only [hubs,hU,hnO]
  have hA0:0<nA:=lt_of_lt_of_le (by positivity) hAhalf
  have hB0:0<mA:=lt_of_lt_of_le (by positivity) hB
  have hkD':kappa≤delta/2:=by
    have hh:=mul_le_mul_of_nonneg_left ho1 hd
    linarith only [hh,hkD]
  have hdn:=mul_le_mul_of_nonneg_right hkD' hn0
  have hdm: kappa*n≤delta*m/2:=by
    have hdn:=mul_le_mul_of_nonneg_right hkD hn0
    have hdm:=mul_le_mul_of_nonneg_left hubs hd
    nlinarith only [hdn,hdm]
  refine ⟨hA,hAhalf,hB,hA0,hB0,by linarith only [hR,hdn],
    by linarith only [hU,hdm],?_,?_⟩
  · have hna:omega*n≤2*nA:=by
      have hh:=mul_le_mul_of_nonneg_right ho1 hn0
      linarith only [hh,hAhalf]
    have hh:=mul_le_mul_of_nonneg_left hna hk
    rw [show (2*kappa/omega)*nA=(2*kappa*nA)/omega by ring]
    apply (le_div_iff₀ ho).mpr
    nlinarith only [hh]
  · have hh:=mul_le_mul_of_nonneg_left hB (show 0≤2*kappa by positivity)
    have he:(2*kappa/omega)*mA=(2*kappa*mA)/omega:=by ring
    rw [he]
    apply (le_div_iff₀ ho).mpr
    nlinarith only [hh]

theorem marked_active_exception_order (omega delta0:ℝ) (ho:0<omega) (hd:0<delta0) (d:ℕ):
    ∃ N:ℕ,1≤N∧∀ n:ℕ,N≤n→∀ nA mA deltaSp:ℝ,
      (n:ℝ)/2≤nA→ omega*n/2≤mA→deltaSp≤delta0/2→
      deltaSp+(6*d+1:ℝ)/nA+1/mA≤delta0:=by
  obtain ⟨N,hN⟩:=exists_nat_gt (max 1 ((4*(6*d+1:ℝ)+4/omega)/delta0))
  have hN1:1<(N:ℝ):=(le_max_left _ _).trans_lt hN
  refine ⟨N,by exact_mod_cast hN1.le,?_⟩
  intro n hn nA mA deltaSp hnA hmA hsp
  have hnreal:(N:ℝ)≤n:=by exact_mod_cast hn
  have hn0:0<(n:ℝ):=by linarith only [hN1,hnreal]
  have hA0:0<nA:=lt_of_lt_of_le (by positivity) hnA
  have hM0:0<mA:=lt_of_lt_of_le (by positivity) hmA
  have hsmall:(4*(6*d+1:ℝ)+4/omega)<delta0*n:=by
    have h:=((le_max_right _ _).trans_lt (hN.trans_le hnreal))
    have hh:4*(6*d+1:ℝ)+4/omega<(n:ℝ)*delta0:=(div_lt_iff₀ hd).mp h
    linarith only [hh]
  have ha:(6*d+1:ℝ)/nA≤2*(6*d+1:ℝ)/n:=by
    have hh:=div_le_div_of_nonneg_left (show 0≤6*(d:ℝ)+1 by positivity) (show 0<(n:ℝ)/2 by positivity) hnA
    convert hh using 1 <;> ring
  have hm:1/mA≤(2/omega)/(n:ℝ):=by
    have hh:=div_le_div_of_nonneg_left (show (0:ℝ)≤1 by norm_num) (show 0<omega*n/2 by positivity) hmA
    convert hh using 1 <;> field_simp <;> ring
  have hs:2*(6*d+1:ℝ)/(n:ℝ)+(2/omega)/(n:ℝ)≤delta0/2:=by
    rw [←add_div]
    apply (div_le_iff₀ hn0).mpr
    rw [show (4:ℝ)/omega=2*(2/omega) by ring] at hsmall
    nlinarith only [hsmall]
  linarith only [ha,hm,hs,hsp]

end Oberwolfach
