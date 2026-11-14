module

public import Oberwolfach.MarkedFixedVortexGeometry
public import Oberwolfach.MarkedPhysicalDeletionRestriction

@[expose] public section
/-! Neighbourhood counts into a fixed vortex set agree exactly under the
subtype embedding, including roots outside the inner set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

theorem marked_vortex_inner_neighbour_image (i:ℕ) (x:markedVortexVertexType Q i):
    (((G.comap (markedVortexVertexEmbedding Q i)).neighborFinset x ∩ markedVortexInnerVertices Q i).image
      (markedVortexVertexEmbedding Q i))=G.neighborFinset x.val ∩ Q.extendedVertices (i+1):=by
  ext v
  constructor
  · intro hv
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hv
    have hh:=Finset.mem_inter.mp hy
    have hf:∀ z,markedVortexVertexEmbedding Q i z=z.val:=fun _=>rfl
    have hxy:=hh.1
    simp only [SimpleGraph.mem_neighborFinset,SimpleGraph.comap_adj] at hxy
    rw [hf,hf] at hxy
    refine Finset.mem_inter.mpr ⟨?_,?_⟩
    · rw [SimpleGraph.mem_neighborFinset,hf]
      exact hxy
    · simpa only [hf] using (Finset.mem_filter.mp hh.2).2
  · intro hv
    obtain ⟨hvG,hvI⟩:=Finset.mem_inter.mp hv
    have hv0:=Q.extendedVertices_subset (show i ≤ i+1 by omega) hvI
    let y:markedVortexVertexType Q i:=⟨v,hv0⟩
    have hy: y∈(G.comap (markedVortexVertexEmbedding Q i)).neighborFinset x ∩ markedVortexInnerVertices Q i:=by
      refine Finset.mem_inter.mpr ⟨?_,?_⟩
      · simp only [SimpleGraph.mem_neighborFinset,SimpleGraph.comap_adj]
        have hf:∀ z,markedVortexVertexEmbedding Q i z=z.val:=fun _=>rfl
        rw [hf,hf]
        simpa only [SimpleGraph.mem_neighborFinset] using hvG
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvI⟩
    exact Finset.mem_image.mpr ⟨y,hy,rfl⟩

theorem marked_vortex_inner_neighbour_card (i:ℕ) (x:markedVortexVertexType Q i):
    ((G.comap (markedVortexVertexEmbedding Q i)).neighborFinset x ∩ markedVortexInnerVertices Q i).card=
      (G.neighborFinset x.val ∩ Q.extendedVertices (i+1)).card:=by
  have hh:=congrArg Finset.card (marked_vortex_inner_neighbour_image Q i x)
  rwa [Finset.card_image_of_injective _ (markedVortexVertexEmbedding Q i).injective] at hh
end Oberwolfach
