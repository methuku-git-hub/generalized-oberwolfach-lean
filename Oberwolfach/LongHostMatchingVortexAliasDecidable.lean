module

public import Oberwolfach.LongHostAdaptiveSharedChoices
public import Oberwolfach.LongHostMatchingVortexCompleteInputs

@[expose] public section
/-! Construct the host continuation directly with its named interface, without
expanding it during later parameter selection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local irreducible] HostMatchingVortexContinuation

theorem long_host_matching_vortex_alias_decidable (L₀:ℕ) (αHost:ℝ) (hα:0<αHost):
    ∃m r k₀:ℕ,7≤m ∧ L₀≤m ∧ Even (m+1) ∧ 2≤r ∧ r+4=m ∧
      r+4+1=(k₀+2)*2 ∧ successorCycleRatio k₀+αHost/4≤1/2+αHost/2 ∧
    ∃A BM:ℝ,0<A ∧ 0<BM ∧
    ∀K d:ℕ,0<K→2≤d→
    ∃BO:Fin K→ℝ,(∀i,0<BO i) ∧ HostMatchingVortexContinuation m K d αHost A BM BO := by
  obtain ⟨m,r,k₀,hm,hLm,heven,hr,hrm,hlen,hmargin,A,BM,hA,hBM,hhost⟩:=
    long_host_matching_vortex_complete_inputs L₀ αHost hα
  refine ⟨m,r,k₀,hm,hLm,heven,hr,hrm,hlen,hmargin,A,BM,hA,hBM,?_⟩
  intro K d hK hd
  obtain ⟨BO,hBO,h⟩:=hhost K d hK hd
  refine ⟨BO,hBO,?_⟩
  unfold HostMatchingVortexContinuation
  intro βQ εQ ρ₀ hb he he1 hρ mLevel
  obtain ⟨vsize,hvsize,hmlevel,hτ⟩:=h βQ εQ ρ₀ hb he he1 hρ mLevel
  refine ⟨vsize,hvsize,hmlevel,?_⟩
  intro τ hτpos
  obtain ⟨N,hN,hNlate⟩:=hτ τ hτpos
  refine ⟨N,hN,?_⟩
  intro Allowed hAllowed hvalid n hn
  have hNn:=hNlate Allowed hAllowed hvalid n hn
  have hdec:referenceWitnessFinDecidable n=instDecidableEqFin n:=Subsingleton.elim _ _
  rw [←hdec] at hNn
  exact hNn
end Oberwolfach
