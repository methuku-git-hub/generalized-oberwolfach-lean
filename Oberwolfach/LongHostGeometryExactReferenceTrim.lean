module

public import Oberwolfach.LongHostGeometryExactReferenceChoices
public import Oberwolfach.LongEarlyMatchingListTrimThreshold

@[expose] public section

/-! Select the marked-cycle length before the host while ensuring that its
first-level reserved-list trim fits the early matching allowance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_host_geometry_exact_reference_with_trim
    (L₀:ℕ) (αHost ρ₀:ℝ) (hα:0<αHost) (hρ:0<ρ₀):
    ∃m r k₀:ℕ,7≤m ∧ L₀≤m ∧ Even (m+1) ∧ 2≤r ∧ r+4=m ∧
      r+4+1=(k₀+2)*2 ∧ successorCycleRatio k₀+αHost/4≤1/2+αHost/2 ∧
    ∃A BM:ℝ,0<A ∧ 0<BM ∧
    ∃αRef γRich ω pstarRef kstar tstar:ℝ,
      αRef=αHost/2 ∧ 0<αRef ∧ 0<γRich ∧ γRich≤1/2 ∧ γRich≤αRef ∧
      successorCycleRatio k₀+αRef/2≤1/2+αRef ∧
      0<ω ∧ 0<pstarRef ∧ 0<kstar ∧ 0<tstar ∧ tstar≤1/100 ∧ tstar≤1 ∧
      4*ω≤ρ₀ ∧ 4*(m:ℝ)*pstarRef≤ρ₀*(1/100) ∧ tstar=(1/100)/(m:ℝ) ∧
      tstar≤(1/100)/(m:ℝ) ∧
      (∀ρ:ℝ,ρ₀≤ρ→kstar≤ρ*(1/100)/2 ∧ kstar≤ρ*((1/100)/(m:ℝ))/2) ∧
      1/(100*((r+4:ℕ):ℝ))≤((min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)/16 ∧
    ∀K d:ℕ,0<K→2≤d→∃BO:Fin K→ℝ,(∀i,0<BO i) ∧
      LongHostMatchingGeometryContinuation m K d αHost A BM BO := by
  obtain ⟨M,hM,htrim⟩:=long_early_matching_list_trim_threshold (αHost/2) ρ₀ (by positivity) hρ
  obtain ⟨m,r,k₀,hm,hmLarge,heven,hr,hrm,hlen,hmargin,A,BM,hA,hBM,hhost⟩:=
    long_host_geometry_exact_reference_choices (max L₀ M) αHost hα
  obtain ⟨αRef,γRich,ω,pstarRef,kstar,tstar,hαEq,hαRef,hγ,hγ1,hγcap,hmargin',hω,hp,hk,ht,ht100,ht1,hωb,hpb,htExact,htcap,hkbound,hcontinue⟩:=hhost ρ₀ hρ
  have hmM:M≤r+4:=by omega
  have htTrim:=htrim (r+4) hmM
  have htTrim' : 1/(100*((r+4:ℕ):ℝ))≤((min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)/16 := by
    simpa only [hαEq] using htTrim
  exact ⟨m,r,k₀,hm,by omega,heven,hr,hrm,hlen,hmargin,A,BM,hA,hBM,
    αRef,γRich,ω,pstarRef,kstar,tstar,hαEq,hαRef,hγ,hγ1,hγcap,hmargin',hω,hp,hk,ht,ht100,ht1,hωb,hpb,htExact,htcap,hkbound,htTrim',hcontinue⟩
end Oberwolfach
