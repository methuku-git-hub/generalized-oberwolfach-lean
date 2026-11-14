module

public import Oberwolfach.OrdinaryVortexBufferedCostGeometry
public import Oberwolfach.OrdinaryFixedVortexCleanupDomainGeometry
public import Oberwolfach.OrdinaryVortexSelectedCostSchedule

@[expose] public section
/-! A fixed envelope for every later protected trace, chosen before the
sample and independent of the actual trace. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_adaptive_edit_envelope
    (ε ρ₀ cap:ℝ) (d:ℕ) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hcap:0<cap):
    ∃rate:ℝ,0<rate ∧ ∀β:ℝ,0 ≤ β → β ≤ 1/4 → ∃m₀:ℕ,1 ≤ m₀ ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D m:ℕ),P.IsRegularOfDegree D → 0<Fintype.card V → 
      (Fintype.card V:ℝ)/2 ≤ D → ρ₀ ≤ initialIndexDensity U D → initialIndexDensity U D ≤ 1 → m₀ ≤ m → 
    ∀(Q:Vortex U P D β ε m) (rateActual:ℝ),0 ≤ rateActual → rateActual ≤ rate → 
    ∀i:ℕ,i+1<Q.length → 
      let loss:=2*((3*d:ℕ):ℝ)+∑j∈Finset.Icc (i+2-2) i,ordinaryVortexSelectedCost Q rateActual j;
      0 ≤ loss ∧ loss ≤ cap*(markedVortexInnerVertices Q (i+1)).card :=by
  obtain ⟨rate,hrate,hwindow⟩:=ordinary_vortex_buffered_cost_from_geometry ε ρ₀ (cap/2) 2 (by omega)
    hε hε1 hρ₀ (by positivity)
  refine ⟨rate,hrate,?_⟩
  intro β hβ hβ1
  obtain ⟨M,hM⟩:=exists_nat_ge (4*((3*d:ℕ):ℝ)/cap)
  obtain ⟨m1,hm1,hwindow⟩:=hwindow β hβ hβ1 0 (by positivity)
  obtain ⟨m2,hm2,hsize⟩:=ordinary_fixed_vortex_cleanup_domain_geometry β ε ρ₀ hβ hβ1 hε hε1 hρ₀ M
  refine ⟨max m1 m2,by omega,?_⟩
  intro V U _ _ _ _ P D m hreg hn hD hρlo hρhi hm Q rateActual hrateActual hrateBound i hi loss
  have hlocal:∀j∈Finset.Icc (i+2-2) i,0 ≤ ordinaryVortexSelectedCost Q rateActual j ∧
      ordinaryVortexSelectedCost Q rateActual j ≤ 4*rate*Fintype.card (markedVortexVertexType Q j⊕markedVortexHubType Q j)+0:=by
    intro j hj
    have hc:(0:ℝ) ≤ Fintype.card (markedVortexVertexType Q j⊕markedVortexHubType Q j):=by positivity
    have hm:=mul_le_mul_of_nonneg_right hrateBound hc
    constructor
    · dsimp [ordinaryVortexSelectedCost];positivity
    · dsimp [ordinaryVortexSelectedCost]
      nlinarith only [hm,mul_nonneg hrateActual hc]
  have hw:=hwindow V U P D m hreg hn hD hρlo hρhi (by omega) Q i hi (ordinaryVortexSelectedCost Q rateActual) hlocal
  have hs:=hsize V U P D m hreg hn hD hρlo hρhi (by omega) Q (i+1) hi
  have hcard: (M:ℝ) ≤ (markedVortexInnerVertices Q (i+1)).card:=by exact_mod_cast hs.2.2.1
  have hfixed:2*((3*d:ℕ):ℝ) ≤ (cap/2)*(markedVortexInnerVertices Q (i+1)).card:=by
    have hh:4*((3*d:ℕ):ℝ) ≤ cap*(M:ℝ):=by simpa [mul_comm] using (div_le_iff₀ hcap).mp hM
    have hmul:=mul_le_mul_of_nonneg_left hcard hcap.le
    nlinarith only [hh,hmul]
  constructor
  · dsimp [loss]; have hfix:(0:ℝ) ≤ 2*((3*d:ℕ):ℝ):=by positivity
    linarith only [hw.1,hfix]
  · dsimp [loss]
    nlinarith only [hw.2.1,hfixed]
end Oberwolfach
