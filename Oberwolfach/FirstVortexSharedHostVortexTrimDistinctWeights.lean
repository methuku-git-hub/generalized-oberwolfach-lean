module

public import Oberwolfach.FirstVortexSharedHostVortexParametersDistinctWeights
public import Oberwolfach.FirstVortexSharedHostVortexParametersDistinctWeights
public import Oberwolfach.FirstVortexTrimLength

@[expose] public section
/-! Fix the actual host construction and the selector's list-trimming margin
using one common cycle length, before the subsequent local choices. -/
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

theorem first_vortex_shared_host_vortex_trim_distinct_weights
    (L₀:ℕ) (αRef ρ₀:ℝ) (hα:0<αRef) (hαCap:2*αRef≤1) (hρ₀:0<ρ₀) (hρ₀one:ρ₀≤1):
    let βList:ℝ:=(min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16;
    ∃m r k₀:ℕ,7≤m ∧ L₀≤m ∧ Even (m+1) ∧ 2≤r ∧ r+4=m ∧
      r+4+1=(k₀+2)*2 ∧ successorCycleRatio k₀+αRef/2≤1/2+αRef ∧
      1/(100*((r+4:ℕ):ℝ))≤βList/16 ∧
    ∃A BM:ℝ,0<A ∧ 0<BM ∧
      (∀K d:ℕ,0<K→2≤d→
        ∃BO:Fin K→ℝ,(∀i,0<BO i) ∧ HostMatchingVortexContinuation m K d (2*αRef) A BM BO) ∧
      FirstVortexSharedVortexTailDistinctWeights r k₀ αRef ρ₀ hα hρ₀ :=by
  intro βList
  obtain ⟨M,hM⟩:=first_vortex_trim_length αRef ρ₀ hα hρ₀
  obtain ⟨m,r,k₀,hm,hLm,heven,hr,hrm,hlen,hmargin,A,BM,hA,hBM,hHost,hTail⟩:=
    first_vortex_shared_host_vortex_parameters_distinct_weights (max L₀ M) αRef ρ₀ hα hαCap hρ₀ hρ₀one
  have hL:L₀≤m:=(le_max_left _ _).trans hLm
  have hbound:M≤m:=(le_max_right _ _).trans hLm
  have htrim:1/(100*((r+4:ℕ):ℝ))≤βList/16:=by
    rw [hrm]
    exact hM m hbound (by omega)
  exact ⟨m,r,k₀,hm,hL,heven,hr,hrm,hlen,hmargin,htrim,A,BM,hA,hBM,hHost,hTail⟩
end Oberwolfach
