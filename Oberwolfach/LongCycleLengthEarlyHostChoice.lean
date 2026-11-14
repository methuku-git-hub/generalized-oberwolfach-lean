module

public import Oberwolfach.LongEarlyMatchingListTrimThreshold
public import Oberwolfach.SuccessorCyclicMargin

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_cycle_length_early_host_choice
    (αRef ρ₀:ℝ) (hα:0<αRef) (hρ:0<ρ₀) (M:ℕ):
    ∃ r k₀:ℕ, M≤r+5 ∧ 2≤r ∧ 7≤r+4 ∧ r+4+1=(k₀+2)*2 ∧
      successorCycleRatio k₀+αRef/2≤1/2+αRef ∧
      1/(100*((r+4:ℕ):ℝ))≤((min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)/16 := by
  obtain ⟨T,hT,htrim⟩:=long_early_matching_list_trim_threshold αRef ρ₀ hα hρ
  obtain ⟨K,hK⟩:=exists_nat_gt (1/αRef)
  let k₀:=max (max M T) (max K 2)
  let r:=2*k₀-1
  have hk2:2≤k₀:=by dsimp [k₀]; omega
  have hkM:M≤k₀:=by dsimp [k₀];omega
  have hkT:T≤k₀:=by dsimp [k₀];omega
  have hkK:K≤k₀:=by dsimp [k₀];omega
  have hlen:r+4+1=(k₀+2)*2:=by dsimp [r];omega
  have hr2:2≤r:=by dsimp [r];omega
  have hm:M≤r+5:=by dsimp [r];omega
  have ht:T≤r+4:=by dsimp [r];omega
  have hKreal:(K:ℝ)≤k₀:=by exact_mod_cast hkK
  have hprod:1≤αRef*(k₀:ℝ):=by
    have hx:1/αRef≤(k₀:ℝ):=hK.le.trans hKreal
    have hx':(1:ℝ)/αRef≤(k₀:ℝ):=hx
    have hh:1≤(k₀:ℝ)*αRef:=(div_le_iff₀ hα).mp hx'
    nlinarith
  have hknonneg:0≤(k₀:ℝ):=by positivity
  have hden:0<(2*((k₀:ℝ)+2)-1):=by linarith
  have hratio:successorCycleRatio k₀≤1/2+αRef/2:=by
    unfold successorCycleRatio
    rw [div_le_iff₀ hden]
    nlinarith [hprod]
  exact ⟨r,k₀,hm,hr2,by omega,hlen,by linarith,htrim (r+4) ht⟩
end Oberwolfach
