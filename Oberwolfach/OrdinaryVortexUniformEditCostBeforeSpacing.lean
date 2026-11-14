module

public import Oberwolfach.OrdinaryVortexAdaptiveEditBeforeSpacing
public import Oberwolfach.OrdinaryVortexUniformEditCostEvents
public import Oberwolfach.OrdinaryVortexAdaptiveEditEnvelope
public import Oberwolfach.OrdinaryVortexUniformAdaptiveEditEvents

@[expose] public section
/-! The uniform all-edit event specializes to the exact protected-trace
cost at every later vortex level, using one deterministic cost-rate cap. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
variable {P:SimpleGraph V} {D mv:ℕ} {β ε:ℝ} (Q:Vortex U P D β ε mv)
  (π:Equiv.Perm V) (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)

theorem ordinary_vortex_uniform_edit_cost_events_before_spacing
    (ε ρ₀ cap:ℝ) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hcap:0<cap):
    ∃rate:ℝ,0<rate ∧ ∀(d:ℕ),∀β:ℝ,0 ≤ β → β ≤ 1/4 → ∃m₀:ℕ,1 ≤ m₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D mv:ℕ),P.IsRegularOfDegree D → 0<Fintype.card V →
      (Fintype.card V:ℝ)/2 ≤ D → ρ₀ ≤ initialIndexDensity U D → initialIndexDensity U D ≤ 1 → m₀ ≤ mv →
    ∀(Q:Vortex U P D β ε mv) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (m:ℕ) (pR pH βe βh b B η:ℝ) (density tR tH:ℕ→ℝ)
      (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
      (rateActual:ℝ),0 ≤ rateActual → rateActual ≤ rate →
    OrdinaryUniformEditWeightEvents Q π hπ m d pR pH cap βe βh b B η density tR tH s j σ →
    ∀i:ℕ,i+1<Q.length →
      let Ledit:=2*((3*d:ℕ):ℝ)+∑k∈Finset.Icc (i+2-2) i,ordinaryVortexSelectedCost Q rateActual k;
      0 ≤ Ledit ∧ Ledit ≤ cap*(markedVortexInnerVertices Q (i+1)).card ∧
      OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent m (P.comap (markedVortexVertexEmbedding Q (i+1)))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q (i+1)))
        (markedVortexInnerVertices Q (i+1)) (markedVortexInnerHubs Q (i+1))
        (markedVortexPermutation Q π hπ (i+1)) d pR pH (density (i+1)) (tR (i+1)) (tH (i+1))
        Ledit βe βh b B η (fun z=>s (markedVortexHubEmbedding Q (i+1) z)) j
        (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q (i+1)) (markedVortexHubEmbedding Q (i+1)) σ) :=by
  obtain ⟨rate,hrate,hgeo⟩:=ordinary_vortex_adaptive_edit_envelope_before_spacing ε ρ₀ cap hε hε1 hρ₀ hcap
  refine ⟨rate,hrate,?_⟩
  intro d β hβ hβ1
  obtain ⟨m₀,hm₀,hgeo⟩:=hgeo d β hβ hβ1
  refine ⟨m₀,hm₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D mv hreg hn hD hρlo hρhi hm Q π hπ m pR pH βe βh b B η density tR tH s j σ
    rateActual hrateActual hrateBound huniform i hi Ledit
  have hcost:=hgeo V U P D mv hreg hn hD hρlo hρhi hm Q rateActual hrateActual hrateBound i hi
  refine ⟨hcost.1,hcost.2,?_⟩
  exact huniform (i+1) hi Ledit hcost.1 hcost.2
end Oberwolfach
