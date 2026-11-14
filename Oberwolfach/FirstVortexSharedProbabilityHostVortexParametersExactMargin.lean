module

public import Oberwolfach.FirstVortexSharedProbabilityVortexTailExactMargin
public import Oberwolfach.LongHostMatchingVortexAliasDecidable

@[expose] public section
/-! Choose the actual host weight/vortex construction and the shared
selector-level parameters with one common cycle length and density margin. -/
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

theorem first_vortex_shared_probability_host_vortex_parameters_exact_margin
    (L₀:ℕ) (αRef ρ₀:ℝ) (hα:0<αRef) (hαCap:2*αRef≤1) (hρ₀:0<ρ₀) (hρ₀one:ρ₀≤1):
    ∃m r k₀:ℕ,7≤m ∧ L₀≤m ∧ Even (m+1) ∧ 2≤r ∧ r+4=m ∧
      r+4+1=(k₀+2)*2 ∧ successorCycleRatio k₀+αRef/2≤1/2+αRef ∧
    ∃A BM:ℝ,0<A ∧ 0<BM ∧
      (∀K d:ℕ,0<K→2≤d→
        ∃BO:Fin K→ℝ,(∀i,0<BO i) ∧ HostMatchingVortexContinuation m K d (2*αRef) A BM BO) ∧
      FirstVortexSharedProbabilityVortexTailExactMargin r k₀ αRef ρ₀ hα hρ₀ :=by
  obtain ⟨c₀,hShared⟩:=first_vortex_shared_probability_vortex_parameters_exact_margin αRef ρ₀ hα hαCap hρ₀ hρ₀one
  obtain ⟨m,r,k₀,hm,hLm,heven,hr,hrm,hlen,hmargin,A,BM,hA,hBM,hHost⟩:=
    long_host_matching_vortex_alias_decidable (max L₀ (c₀+5)) (2*αRef) (by positivity)
  have hL:L₀≤m:=le_trans (le_max_left _ _) hLm
  have hc:c₀≤r+5:=by have hh:=(le_max_right L₀ (c₀+5)).trans hLm;omega
  have hmargin':successorCycleRatio k₀+αRef/2≤1/2+αRef:=by nlinarith
  have hTail:FirstVortexSharedProbabilityVortexTailExactMargin r k₀ αRef ρ₀ hα hρ₀:=hShared r hr hc k₀ hlen hmargin'
  exact ⟨m,r,k₀,hm,hL,heven,hr,hrm,hlen,hmargin',A,BM,hA,hBM,hHost,hTail⟩
end Oberwolfach
