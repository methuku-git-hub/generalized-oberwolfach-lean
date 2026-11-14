module

public import Oberwolfach.MarkedFixedVortexGeometry
public import Oberwolfach.VortexProtectedGeometry

@[expose] public section
/-! The pre-exposure vortex sets satisfy the active-event subset and
geometric-size hypotheses with their original independently rounded sizes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_inner_cardinalities (i:ℕ):
    (markedVortexInnerVertices Q i).card=(Q.extendedVertices (i+1)).card ∧
    (markedVortexDeeperVertices Q i).card=(Q.extendedVertices (i+2)).card ∧
    (markedVortexInnerHubs Q i).card=(Q.extendedIndices (i+1)).card ∧
    (markedVortexDeeperHubs Q i).card=(Q.extendedIndices (i+2)).card:=by
  obtain ⟨hI,hT,hJ,hW⟩:=marked_vortex_inner_images Q i
  constructor
  · rw [←hI,Finset.card_image_of_injective _ (markedVortexVertexEmbedding Q i).injective]
  constructor
  · rw [←hT,Finset.card_image_of_injective _ (markedVortexVertexEmbedding Q i).injective]
  constructor
  · rw [←hJ,Finset.card_image_of_injective _ (markedVortexHubEmbedding Q i).injective]
  · rw [←hW,Finset.card_image_of_injective _ (markedVortexHubEmbedding Q i).injective]

theorem marked_vortex_fixed_active_geometry (he:0≤ε) (i:ℕ):
    markedVortexDeeperVertices Q i⊆markedVortexInnerVertices Q i ∧
    markedVortexDeeperHubs Q i⊆markedVortexInnerHubs Q i ∧
    (((markedVortexDeeperVertices Q i).card:ℝ)≤ε*(markedVortexInnerVertices Q i).card) ∧
    (((markedVortexDeeperHubs Q i).card:ℝ)≤ε*(markedVortexInnerHubs Q i).card) ∧
    (((markedVortexInnerVertices Q (i+1)).card:ℝ)≤ε*(markedVortexInnerVertices Q i).card) ∧
    (((markedVortexInnerHubs Q (i+1)).card:ℝ)≤ε*(markedVortexInnerHubs Q i).card):=by
  have hv:markedVortexDeeperVertices Q i⊆markedVortexInnerVertices Q i:=by
    intro x hx
    have hh: x.val∈Q.extendedVertices (i+2):=(Finset.mem_filter.mp hx).2
    have hsub:=Q.extendedVertices_subset (show i+1 ≤ i+2 by omega)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsub hh⟩
  have hu:markedVortexDeeperHubs Q i⊆markedVortexInnerHubs Q i:=by
    intro x hx
    have hh:x.val∈Q.extendedIndices (i+2):=(Finset.mem_filter.mp hx).2
    have hsub:=Q.extendedIndices_subset (show i+1 ≤ i+2 by omega)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsub hh⟩
  obtain ⟨hI,hT,hJ,hW⟩:=marked_vortex_inner_cardinalities Q i
  obtain ⟨hI',_,hJ',_⟩:=marked_vortex_inner_cardinalities Q (i+1)
  have hstep:=Q.extended_successor_size_bounds he (i+1)
  refine ⟨hv,hu,?_,?_,?_,?_⟩
  · rw [hT,hI]
    simpa only [Nat.add_assoc] using hstep.1
  · rw [hW,hJ]
    simpa only [Nat.add_assoc] using hstep.2
  · rw [hI',hI]
    simpa only [Nat.add_assoc] using hstep.1
  · rw [hJ',hJ]
    simpa only [Nat.add_assoc] using hstep.2
end Oberwolfach
