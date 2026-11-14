module

public import Oberwolfach.OrdinaryAdaptiveHubUniformEditEvent
public import Oberwolfach.OrdinaryVortexAsymmetricMatchingScales

@[expose] public section
/-! A single all-level event with an earlier edit envelope supplies each
later actual profile event uniformly, on the same raw outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_uniform_adaptive_edit_events
    (ε ρ₀ eParent hParent ζ:ℝ) (hε:0<ε) (hρ₀:0<ρ₀) (he:0<eParent) (hh:0<hParent) (hζ:0<ζ):
    ∃eEvent hEvent cap:ℝ,0<eEvent ∧ 0<hEvent ∧ 0<cap ∧ cap ≤ ζ ∧
      eEvent ≤ eParent ∧ hEvent ≤ hParent ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P:SimpleGraph V) (D mv:ℕ) (β:ℝ),P.IsRegularOfDegree D → 0<Fintype.card V →
      (Fintype.card V:ℝ)/2 ≤ D → ρ₀ ≤ initialIndexDensity U D → initialIndexDensity U D ≤ 1 →
      0 ≤ β → β ≤ 1/4 → 0<mv →
    ∀(Q:Vortex U P D β ε mv) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i ↔ x∈Q.extendedVertices i)
      (m d:ℕ) (pR pH b B η:ℝ) (density tR tH:ℕ→ℝ) (s:U→Color→ℝ) (j:Color)
      (σ:RawWheelOutcome V U Γ Color),
    (∀i,i<Q.length →
      OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent m (P.comap (markedVortexVertexEmbedding Q i))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) (markedVortexPermutation Q π hπ i) d
        pR pH (density i) (tR i) (tH i) (cap*(markedVortexInnerVertices Q i).card)
        (eEvent*ε) (hEvent*ε) b B η (fun z=>s (markedVortexHubEmbedding Q i z)) j
        (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ)) →
    ∀i,i<Q.length → ∀Lold:ℝ,0 ≤ Lold → Lold ≤ cap*(markedVortexInnerVertices Q i).card →
      OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent m (P.comap (markedVortexVertexEmbedding Q i))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) (markedVortexPermutation Q π hπ i) d
        pR pH (density i) (tR i) (tH i) Lold (eParent*ε) (hParent*ε) b B η
        (fun z=>s (markedVortexHubEmbedding Q i z)) j
        (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ) :=by
  obtain ⟨eEvent,hEvent,cap0,heEvent,hhEvent,hcap0,heBound,hhBound,htransfer⟩:=
    ordinary_adaptive_hub_uniform_edit_event eParent hParent he hh
  let cap:ℝ:=min cap0 ζ
  have hcap:0<cap:=by dsimp [cap];positivity
  have hcap0':cap ≤ cap0:=min_le_left _ _
  have hcapζ:cap ≤ ζ:=min_le_right _ _
  refine ⟨eEvent,hEvent,cap,heEvent,hhEvent,hcap,hcapζ,heBound,hhBound,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D mv β hreg hn hD hρlo hρhi hβ hβ1 hmv Q π hπ
    m d pR pH b B η density tR tH s j σ hbase i hi Lold hLold hL
  have hsc:=ordinary_vortex_asymmetric_matching_scales Q hreg hn hD hρ₀ hρlo hρhi hβ hβ1 hε hmv i hi
    1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hI:((markedVortexInnerVertices Q i).card:ℝ) ≤
      ε*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i):=by
    simpa using hsc.2.2.2.2.2.2.2.2
  have hcapI:cap*(markedVortexInnerVertices Q i).card ≤ cap0*(markedVortexInnerVertices Q i).card:=
    mul_le_mul_of_nonneg_right hcap0' (by positivity)
  exact htransfer (markedVortexVertexType Q i) (markedVortexHubType Q i) Γ Color m
    (P.comap (markedVortexVertexEmbedding Q i))
    ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
    (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) (markedVortexPermutation Q π hπ i) d
    pR pH (density i) (tR i) (tH i) ε Lold (cap*(markedVortexInnerVertices Q i).card) b B η
    (fun z=>s (markedVortexHubEmbedding Q i z)) j
    (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ)
    hε.le hLold hL hI hcapI (hbase i hi)
end Oberwolfach
