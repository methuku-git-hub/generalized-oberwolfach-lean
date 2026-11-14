module

public import Oberwolfach.MarkedFixedVortexGeometry
public import Oberwolfach.OrdinaryVortexBufferedRootSizes

@[expose] public section
/-! Buffered deeper domains are fixed subsets of the actual vortex parent,
    with the same embeddings and an explicit geometric size bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {P:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U P D β ε m)

def ordinaryVortexBufferedVertices (i buffer:ℕ):Finset (markedVortexVertexType Q i):=
  Finset.univ.filter (fun v=>v.val∈Q.extendedVertices (i+buffer))

def ordinaryVortexBufferedHubs (i buffer:ℕ):Finset (markedVortexHubType Q i):=
  Finset.univ.filter (fun u=>u.val∈Q.extendedIndices (i+buffer))

theorem ordinary_vortex_buffered_images (i buffer:ℕ):
    (ordinaryVortexBufferedVertices Q i buffer).image (markedVortexVertexEmbedding Q i)=Q.extendedVertices (i+buffer) ∧
    (ordinaryVortexBufferedHubs Q i buffer).image (markedVortexHubEmbedding Q i)=Q.extendedIndices (i+buffer) :=by
  constructor
  · ext x
    constructor
    · intro hx
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hv).2
    · intro hx
      have hx0:=Q.extendedVertices_subset (show i ≤ i+buffer by omega) hx
      exact Finset.mem_image.mpr ⟨⟨x,hx0⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,rfl⟩
  · ext u
    constructor
    · intro hu
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hu
      exact (Finset.mem_filter.mp hv).2
    · intro hu
      have hu0:=Q.extendedIndices_subset (show i ≤ i+buffer by omega) hu
      exact Finset.mem_image.mpr ⟨⟨u,hu0⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩,rfl⟩

theorem ordinary_vortex_buffered_nested (i buffer:ℕ) (hbuffer:2≤buffer):
    ordinaryVortexBufferedVertices Q i buffer⊆markedVortexDeeperVertices Q i ∧
    ordinaryVortexBufferedHubs Q i buffer⊆markedVortexDeeperHubs Q i ∧
    ordinaryVortexBufferedVertices Q i buffer⊆markedVortexInnerVertices Q i ∧
    ordinaryVortexBufferedHubs Q i buffer⊆markedVortexInnerHubs Q i :=by
  refine ⟨?_,?_,?_,?_⟩
  · intro v hv
    simp only [ordinaryVortexBufferedVertices,markedVortexDeeperVertices,Finset.mem_filter,Finset.mem_univ,true_and] at hv ⊢
    exact Q.extendedVertices_subset (by omega) hv
  · intro u hu
    simp only [ordinaryVortexBufferedHubs,markedVortexDeeperHubs,Finset.mem_filter,Finset.mem_univ,true_and] at hu ⊢
    exact Q.extendedIndices_subset (by omega) hu
  · intro v hv
    simp only [ordinaryVortexBufferedVertices,markedVortexInnerVertices,Finset.mem_filter,Finset.mem_univ,true_and] at hv ⊢
    exact Q.extendedVertices_subset (by omega) hv
  · intro u hu
    simp only [ordinaryVortexBufferedHubs,markedVortexInnerHubs,Finset.mem_filter,Finset.mem_univ,true_and] at hu ⊢
    exact Q.extendedIndices_subset (by omega) hu

theorem ordinary_vortex_buffered_card_bound (hε:0≤ε) (i buffer:ℕ)
    (hU:Fintype.card (markedVortexHubType Q i)≤Fintype.card (markedVortexVertexType Q i)):
    ((ordinaryVortexBufferedVertices Q i buffer).card:ℝ)+(ordinaryVortexBufferedHubs Q i buffer).card≤
      2*ε^buffer*Fintype.card (markedVortexVertexType Q i) :=by
  have himg:=ordinary_vortex_buffered_images Q i buffer
  have hV:(ordinaryVortexBufferedVertices Q i buffer).card=(Q.extendedVertices (i+buffer)).card:=by
    rw [←himg.1,Finset.card_image_of_injective _ (markedVortexVertexEmbedding Q i).injective]
  have hH:(ordinaryVortexBufferedHubs Q i buffer).card=(Q.extendedIndices (i+buffer)).card:=by
    rw [←himg.2,Finset.card_image_of_injective _ (markedVortexHubEmbedding Q i).injective]
  have hU':(Q.extendedIndices i).card≤(Q.extendedVertices i).card:=by simpa only [markedVortexHubType,markedVortexVertexType,Fintype.card_coe] using hU
  have h:=ordinary_vortex_buffered_root_sizes P D m β ε Q hε i buffer hU'
  simpa only [hV,hH,markedVortexVertexType,Fintype.card_coe] using h
end Oberwolfach
