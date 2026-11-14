module

public import Oberwolfach.LongHostMatchingVortexAliasDecidable
public import Oberwolfach.LongPrescribedMatchingHubMargins

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach

theorem long_host_with_prescribed_matching_hub_margins
    (L₀:ℕ) (αHost ρ₀:ℝ) (hαHost:0<αHost) (hρ₀:0<ρ₀):
    ∃b α:ℝ,0<b ∧ 0<α ∧ α/16≤b ∧
      (∀ρ:ℝ,ρ₀/4≤ρ→b≤(ρ/40000)/16) ∧
    ∃m r k₀:ℕ,7≤m ∧ L₀≤m ∧ 4/(m:ℝ)≤b/2 ∧ Even (m+1) ∧ 2≤r ∧ r+4=m ∧
      r+4+1=(k₀+2)*2 ∧ successorCycleRatio k₀+αHost/4≤1/2+αHost/2 ∧
    ∃A BM:ℝ,0<A ∧ 0<BM ∧
    ∀K d:ℕ,0<K→2≤d→∃BO:Fin K→ℝ,(∀i,0<BO i) ∧ HostMatchingVortexContinuation m K d αHost A BM BO:=by
  obtain ⟨b,α,hb,hα,hαb,hρ,L,hL,hbound⟩:=long_prescribed_matching_hub_margins (ρ₀/4) (by positivity)
  obtain ⟨m,r,k₀,hm,hLm,heven,hr,hrm,hlen,hmargin,A,BM,hA,hBM,hhost⟩:=
    long_host_matching_vortex_alias_decidable (max L₀ L) αHost hαHost
  have hL0:L₀≤m:=le_trans (le_max_left _ _) hLm
  have hL':L≤m:=le_trans (le_max_right _ _) hLm
  exact ⟨b,α,hb,hα,hαb,hρ,m,r,k₀,hm,hL0,hbound m hL',heven,hr,hrm,hlen,hmargin,A,BM,hA,hBM,hhost⟩
end Oberwolfach
