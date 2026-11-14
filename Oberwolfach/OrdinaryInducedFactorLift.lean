module

public import Oberwolfach.OrdinaryFullInducedCycleEmbedding

@[expose] public section
/-! Lift a factor on the induced domain to the ambient local cycle family,
preserving disjointness, its exact vertex set, and avoidance of conflicts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {r:ℕ}

theorem ordinary_induced_factor_lift
    (Q F K:SimpleGraph V) (T:Finset V) (Y:Finset {v:V // v∈T})
    (D:Finset (LocalOrdinaryCycle (Q.induce (T:Set V)) (F.induce (T:Set V)) Finset.univ r))
    (hdis:∀C∈D,∀C'∈D,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C'))
    (hcover:D.biUnion localOrdinaryVertices=Y)
    (havoid:∀C∈D,∀x∈localOrdinaryVertices C,∀y∈localOrdinaryVertices C,
      ¬(K.induce (T:Set V)).Adj x y):
    ∃D':Finset (LocalOrdinaryCycle Q F T r),
      (∀C∈D',∀C'∈D',C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C')) ∧
      D'.biUnion localOrdinaryVertices=Y.image Subtype.val ∧
      (∀C∈D',∀x∈localOrdinaryVertices C,∀y∈localOrdinaryVertices C,¬K.Adj x y):=by
  let e:=ordinaryFullInducedCycleEmbedding (r:=r) Q F T
  refine ⟨D.image e,?_,?_,?_⟩
  · intro C hC C' hC' hne
    obtain ⟨A,hA,rfl⟩:=Finset.mem_image.mp hC
    obtain ⟨B,hB,rfl⟩:=Finset.mem_image.mp hC'
    have hAB:A≠B:=by intro he;apply hne;rw [he]
    have hd:=hdis A hA B hB hAB
    rw [ordinary_full_induced_cycle_embedding_vertices,ordinary_full_induced_cycle_embedding_vertices]
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨x,hx,hxv⟩:=Finset.mem_image.mp hv
    obtain ⟨y,hy,hyv⟩:=Finset.mem_image.mp hw
    have hxy:x=y:=Subtype.ext (hxv.trans hyv.symm)
    exact Finset.disjoint_left.mp hd hx (hxy ▸ hy)
  · ext v
    constructor
    · intro hv
      obtain ⟨C,hC,hvC⟩:=Finset.mem_biUnion.mp hv
      obtain ⟨A,hA,rfl⟩:=Finset.mem_image.mp hC
      rw [ordinary_full_induced_cycle_embedding_vertices] at hvC
      obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hvC
      apply Finset.mem_image.mpr
      refine ⟨x,?_,rfl⟩
      rw [←hcover]
      exact Finset.mem_biUnion.mpr ⟨A,hA,hx⟩
    · intro hv
      obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hv
      rw [←hcover] at hx
      obtain ⟨A,hA,hxA⟩:=Finset.mem_biUnion.mp hx
      apply Finset.mem_biUnion.mpr
      refine ⟨e A,Finset.mem_image.mpr ⟨A,hA,rfl⟩,?_⟩
      rw [ordinary_full_induced_cycle_embedding_vertices]
      exact Finset.mem_image.mpr ⟨x,hxA,rfl⟩
  · intro C hC x hx y hy
    obtain ⟨A,hA,rfl⟩:=Finset.mem_image.mp hC
    rw [ordinary_full_induced_cycle_embedding_vertices] at hx hy
    obtain ⟨x',hx',rfl⟩:=Finset.mem_image.mp hx
    obtain ⟨y',hy',rfl⟩:=Finset.mem_image.mp hy
    exact havoid A hA x' hx' y' hy'
end Oberwolfach
