module

public import Oberwolfach.FirstVortexOriginalMarginHostConcrete
public import Oberwolfach.FirstVortexSharedVortexHighProbabilityNumericReady

@[expose] public section
/-! Choose the high-probability structural and level selectors from the
original host margin and lower density before any failure allowance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxRecDepth 32768
set_option maxHeartbeats 120000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem first_vortex_original_margin_high_probability_selector
    (α₀ ρstar εmax:ℝ) (hα₀:0<α₀) (hρstar:0<ρstar) (hεmax:0<εmax):
    ∃ (αRef κL ρ₀:ℝ) (href:0<αRef) (hρ:0<ρ₀),
      2*αRef≤1 ∧ 2*αRef≤α₀/2 ∧ (2*αRef)/100000≤εmax ∧ 0<κL ∧ ρ₀≤1 ∧ ρ₀≤ρstar ∧
      (∀δ D:ℝ,∀n:ℕ,(δ+α₀/2)*(n:ℝ)≤D→(δ+2*αRef)*(n:ℝ)≤D) ∧
    ∀L₀:ℕ,
    let βList:ℝ:=(min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
    ∃m r k₀:ℕ,7≤m ∧ L₀≤m ∧ Even (m+1) ∧ 2≤r ∧ r+4=m ∧
      r+4+1=(k₀+2)*2 ∧ successorCycleRatio k₀+αRef/2≤1/2+αRef ∧
      1/(100*((r+4:ℕ):ℝ))≤βList/16 ∧
    ∃A BM:ℝ,0<A ∧ 0<BM ∧
      (∀K d:ℕ,0<K→2≤d→∃BO:Fin K→ℝ,(∀i,0<BO i) ∧ HostMatchingVortexContinuation m K d (2*αRef) A BM BO) ∧
      FirstVortexSharedVortexHighProbabilityNumericReady r k₀ αRef ρ₀ href hρ :=by
  let α:ℝ:=min α₀ (min (500*ρstar) (50000*εmax))
  have hα:0<α:=by dsimp [α];positivity
  have hαle:α≤α₀:=by dsimp [α];exact min_le_left _ _
  have hαrho:α≤500*ρstar:=by dsimp [α];exact (min_le_right _ _).trans (min_le_left _ _)
  have hαeps:α≤50000*εmax:=by dsimp [α];exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨αRef,κL,ρ₀,href,hρ,hrefCap,hrefAlpha,hκ,hκcap,hρone,hρκ,hmargin,hHost⟩:=
    first_vortex_original_margin_host_concrete α hα
  have hρcap:ρ₀≤ρstar:=by linarith
  have hrefOriginal:2*αRef≤α₀/2:=by linarith
  have hrefEps:(2*αRef)/100000≤εmax:=by linarith
  have hmarginOriginal:∀δ D:ℝ,∀n:ℕ,(δ+α₀/2)*(n:ℝ)≤D→(δ+2*αRef)*(n:ℝ)≤D:=by
    intro δ D n hdeg
    apply hmargin δ D n
    have hn:0≤(n:ℝ):=by positivity
    nlinarith only [hdeg,mul_nonneg (by linarith only [hαle] : 0≤(α₀-α)/2) hn]
  obtain ⟨c₀,hHigh⟩:=first_vortex_shared_vortex_high_probability_parameters αRef ρ₀ href hrefCap hρ hρone
  refine ⟨αRef,κL,ρ₀,href,hρ,hrefCap,hrefOriginal,hrefEps,hκ,hρone,hρcap,hmarginOriginal,?_⟩
  intro L₀ βList
  obtain ⟨m,r,k₀,hm,hL,heven,hr,hrm,hlen,hcycle,htrim,A,BM,hA,hBM,hHostCont,hOld⟩:=hHost (max L₀ c₀)
  have hc₀:c₀≤r+5:=by omega
  have hTail:FirstVortexSharedVortexHighProbabilityTail r k₀ αRef ρ₀ href hρ:=
    hHigh r hr hc₀ k₀ hlen hcycle
  have hTransfer:=first_vortex_shared_vortex_high_probability_transfer_ready r k₀ αRef ρ₀ href hρ hTail
  have hLevel:=first_vortex_shared_vortex_high_probability_level_ready r k₀ αRef ρ₀ href hρ hTransfer
  have hExplicit:=first_vortex_shared_vortex_high_probability_explicit_ready r k₀ αRef ρ₀ href hρ hLevel
  have hSelected:=first_vortex_shared_vortex_high_probability_selected_ready r k₀ αRef ρ₀ href hρ hExplicit
  have hReady:=first_vortex_shared_vortex_high_probability_caller_ready r k₀ αRef ρ₀ href hρ hSelected
  have hNew:=first_vortex_shared_vortex_high_probability_numeric_ready r k₀ αRef ρ₀ href hρ hReady
  exact ⟨m,r,k₀,hm,by omega,heven,hr,hrm,hlen,hcycle,htrim,A,BM,hA,hBM,hHostCont,hNew⟩
end Oberwolfach
