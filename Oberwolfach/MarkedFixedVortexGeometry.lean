module

public import Oberwolfach.VortexPermutation

@[expose] public section
/-! Fixed, pre-exposure domains and their embeddings obtained directly from
a vortex and a permutation preserving its sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)

abbrev markedVortexVertexType (i:ℕ):Type:={x:V // x∈Q.extendedVertices i}
abbrev markedVortexHubType (i:ℕ):Type:={u:U // u∈Q.extendedIndices i}

def markedVortexVertexEmbedding (i:ℕ):markedVortexVertexType Q i ↪o V where
  toFun x:=x.val
  inj':=Subtype.val_injective
  map_rel_iff':=by intro x y; rfl

def markedVortexHubEmbedding (i:ℕ):markedVortexHubType Q i ↪ U :=
  ⟨Subtype.val,Subtype.val_injective⟩

def markedVortexInnerVertices (i:ℕ):Finset (markedVortexVertexType Q i):=
  Finset.univ.filter (fun x=>x.val∈Q.extendedVertices (i+1))

def markedVortexDeeperVertices (i:ℕ):Finset (markedVortexVertexType Q i):=
  Finset.univ.filter (fun x=>x.val∈Q.extendedVertices (i+2))

def markedVortexInnerHubs (i:ℕ):Finset (markedVortexHubType Q i):=
  Finset.univ.filter (fun u=>u.val∈Q.extendedIndices (i+1))

def markedVortexDeeperHubs (i:ℕ):Finset (markedVortexHubType Q i):=
  Finset.univ.filter (fun u=>u.val∈Q.extendedIndices (i+2))

theorem marked_vortex_inner_images (i:ℕ):
    (markedVortexInnerVertices Q i).image (markedVortexVertexEmbedding Q i)=Q.extendedVertices (i+1) ∧
    (markedVortexDeeperVertices Q i).image (markedVortexVertexEmbedding Q i)=Q.extendedVertices (i+2) ∧
    (markedVortexInnerHubs Q i).image (markedVortexHubEmbedding Q i)=Q.extendedIndices (i+1) ∧
    (markedVortexDeeperHubs Q i).image (markedVortexHubEmbedding Q i)=Q.extendedIndices (i+2):=by
  constructor
  · ext x
    constructor
    · intro hx
      obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hy).2
    · intro hx
      have hx0:=Q.extendedVertices_subset (show i ≤ i+1 by omega) hx
      exact Finset.mem_image.mpr ⟨⟨x,hx0⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,rfl⟩
  constructor
  · ext x
    constructor
    · intro hx
      obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hy).2
    · intro hx
      have hx0:=Q.extendedVertices_subset (show i ≤ i+2 by omega) hx
      exact Finset.mem_image.mpr ⟨⟨x,hx0⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,rfl⟩
  constructor
  · ext u
    constructor
    · intro hu
      obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hu
      exact (Finset.mem_filter.mp hy).2
    · intro hu
      have hu0:=Q.extendedIndices_subset (show i ≤ i+1 by omega) hu
      exact Finset.mem_image.mpr ⟨⟨u,hu0⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩,rfl⟩
  · ext u
    constructor
    · intro hu
      obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hu
      exact (Finset.mem_filter.mp hy).2
    · intro hu
      have hu0:=Q.extendedIndices_subset (show i ≤ i+2 by omega) hu
      exact Finset.mem_image.mpr ⟨⟨u,hu0⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩,rfl⟩

def markedVortexPermutation (π:Equiv.Perm V)
    (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (i:ℕ):
    Equiv.Perm (markedVortexVertexType Q i):=π.subtypePerm (hπ i)

theorem marked_vortex_permutation_compatibility (π:Equiv.Perm V)
    (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (i:ℕ):
    (∀ x,markedVortexVertexEmbedding Q i (markedVortexPermutation Q π hπ i x)=π (markedVortexVertexEmbedding Q i x)) ∧
    (∀ x,markedVortexPermutation Q π hπ i x∈markedVortexInnerVertices Q i↔x∈markedVortexInnerVertices Q i) ∧
    (∀ x,markedVortexPermutation Q π hπ i x∈markedVortexDeeperVertices Q i↔x∈markedVortexDeeperVertices Q i):=by
  constructor
  · intro x
    rfl
  constructor
  · intro x
    simp only [markedVortexInnerVertices,Finset.mem_filter,Finset.mem_univ,true_and]
    change π x.val∈Q.extendedVertices (i+1)↔x.val∈Q.extendedVertices (i+1)
    exact hπ (i+1) x.val
  · intro x
    simp only [markedVortexDeeperVertices,Finset.mem_filter,Finset.mem_univ,true_and]
    change π x.val∈Q.extendedVertices (i+2)↔x.val∈Q.extendedVertices (i+2)
    exact hπ (i+2) x.val
end Oberwolfach
