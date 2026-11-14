module

public import Oberwolfach.LongCycleLengthEarlyHostChoice

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

/-- The length can be chosen after a positive residual-list margin is fixed,
while retaining the parent geometry and the original early-list margin. -/
theorem long_cycle_length_with_residual_trim
    (αRef ρ₀ lamList:ℝ) (hα:0<αRef) (hρ:0<ρ₀) (hlam:0<lamList) (M:ℕ):
    ∃ r k₀:ℕ, M≤r+5 ∧ 2≤r ∧ 7≤r+4 ∧ r+4+1=(k₀+2)*2 ∧
      successorCycleRatio k₀+αRef/2≤1/2+αRef ∧
      1/(100*((r+4:ℕ):ℝ))≤((min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)/16 ∧
      1/(100*((r+4:ℕ):ℝ))≤lamList/4 :=by
  obtain ⟨T,hT⟩:=exists_nat_gt (1/(25*lamList))
  obtain ⟨r,k₀,hM,hr,hm,hlen,hratio,htrim⟩:=
    long_cycle_length_early_host_choice αRef ρ₀ hα hρ (max M (T+1))
  have hTr:T≤r+4:=by omega
  have hTrR:(T:ℝ)≤((r+4:ℕ):ℝ):=by exact_mod_cast hTr
  have hden:0<(100:ℝ)*((r+4:ℕ):ℝ):=by positivity
  have hprod:1≤25*lamList*((r+4:ℕ):ℝ):=by
    have hx:(1:ℝ)/(25*lamList)≤((r+4:ℕ):ℝ):=hT.le.trans hTrR
    have hh:1≤((r+4:ℕ):ℝ)*(25*lamList):=(div_le_iff₀ (by positivity)).mp hx
    nlinarith
  refine ⟨r,k₀,by omega,hr,hm,hlen,hratio,htrim,?_⟩
  apply (div_le_iff₀ hden).2
  nlinarith
end Oberwolfach
