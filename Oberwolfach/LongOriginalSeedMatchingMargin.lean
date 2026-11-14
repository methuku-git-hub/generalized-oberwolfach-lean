module

public import Oberwolfach.LongOriginalSeedParameters
public import Oberwolfach.SuccessorCyclicMargin

@[expose] public section
/-! Any sufficiently long even successor seed has the exact length and
reference-margin inequalities used by the long matching selector. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem long_original_seed_matching_margin
    (αRef βList:ℝ) (hα:0<αRef) (hβ:0<βList):
    ∃N:ℕ,1≤N ∧ ∀m:ℕ,N≤m→7≤m→Even (m+1)→
    ∃r k₀:ℕ,2≤r ∧ m=r+4 ∧ r+4+1=(k₀+2)*2 ∧
      successorCycleRatio k₀+αRef/2≤1/2+αRef ∧
      1/(100*((r+4:ℕ):ℝ))≤βList/16:=by
  obtain ⟨N,hN⟩:=exists_nat_gt (max (1/αRef) (16/(100*βList)))
  refine ⟨max 1 N,by omega,?_⟩
  intro m hmN hm heven
  obtain ⟨r,k₀,hr,hrm,hlen,_⟩:=long_original_seed_length_parameters m hm heven
  refine ⟨r,k₀,hr,hrm,hlen,?_⟩
  have hmpos:0<(m:ℝ):=by exact_mod_cast (show 0<m by omega)
  have hmN':(N:ℝ)≤m:=by exact_mod_cast (show N≤m by omega)
  have hN1:1/αRef≤(m:ℝ):=(le_max_left _ _).trans (hN.le.trans hmN')
  have hN2:16/(100*βList)≤(m:ℝ):=(le_max_right _ _).trans (hN.le.trans hmN')
  have hprod:1≤αRef*m:=by
    have hh:=(div_le_iff₀ hα).mp hN1
    nlinarith only [hh]
  have hprod2:16≤(100*βList)*m:=by
    have hh:=(div_le_iff₀ (by positivity:0<100*βList)).mp hN2
    nlinarith only [hh]
  have hlen':(m:ℝ)+1=((k₀:ℝ)+2)*2:=by
    have ht:m+1=(k₀+2)*2:=by omega
    exact_mod_cast ht
  have hden:0<2*((k₀:ℝ)+2)-1:=by nlinarith only [hlen',hmpos]
  have hratio:successorCycleRatio k₀≤1/2+αRef/2:=by
    unfold successorCycleRatio
    apply (div_le_iff₀ hden).2
    nlinarith only [hprod,hlen']
  constructor
  · linarith only [hratio]
  · rw [←hrm]
    apply (div_le_iff₀ (by positivity:0<100*(m:ℝ))).2
    nlinarith only [hprod2]
end Oberwolfach
