module

public import Oberwolfach.BufferedFactorFamilyCompletion
public import Oberwolfach.FullFactorSetPackingToDecomposition

@[expose] public section
/-! Finish the exact regular-host decomposition from compatible buffered
path and complement embeddings, with their edge-disjointness hypotheses. -/
set_option autoImplicit false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_factor_family_gives_decomposition
    {N D:ℕ} (hEven:Even D) (H:SimpleGraph (Fin N)) (hH:H.IsRegularOfDegree D)
    (G:Fin (D/2)→SimpleGraph (Fin N)) (hG:∀u,(G u).IsRegularOfDegree 2)
    (I:Fin (D/2)→Type*) [∀u,Fintype (I u)]
    (n:∀u,I u→ℕ)
    (ext:∀u (i:I u),Fin (n u i+5)↪(Fin N)) (inner:∀u (i:I u),Fin (n u i+1)↪(Fin N))
    (hinner:∀u i p,inner u i p=ext u i ⟨p.val+2,by omega⟩)
    (hwalk:∀u i,∃p:(G u).Walk (ext u i ⟨0,by omega⟩) (ext u i ⟨n u i+4,by omega⟩),
      p.length=n u i+4 ∧ p.support=List.ofFn (ext u i))
    (fA:∀u,{x // x∈bufferedPathFullDomain (n u) (inner u)}↪(Fin N))
    (fC:∀u,{x // x∉bufferedPathStrictInterior (n u) (inner u)}↪(Fin N))
    (hA:∀u x y (hx:x∈bufferedPathFullDomain (n u) (inner u)) (hy:y∈bufferedPathFullDomain (n u) (inner u)),
      (G u).Adj x y→H.Adj (fA u ⟨x,hx⟩) (fA u ⟨y,hy⟩))
    (hC:∀u x y (hx:x∉bufferedPathStrictInterior (n u) (inner u)) (hy:y∉bufferedPathStrictInterior (n u) (inner u)),
      (G u).Adj x y→H.Adj (fC u ⟨x,hx⟩) (fC u ⟨y,hy⟩))
    (hend:∀u i (p:Fin (n u i+1)),(p=0 ∨ p=Fin.last (n u i))→
      ∀ hpD:inner u i p∉bufferedPathStrictInterior (n u) (inner u),
      fA u ⟨inner u i p,buffered_path_vertex_mem_domain (n u) (inner u) i p⟩=fC u ⟨inner u i p,hpD⟩)
    (hdis:∀u x (hx:x∈bufferedPathStrictInterior (n u) (inner u)) y (hy:y∉bufferedPathStrictInterior (n u) (inner u)),
      fA u ⟨x,buffered_strict_interior_subset_domain (n u) (inner u) hx⟩≠fC u ⟨y,hy⟩)
    (hAA:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x // x∈bufferedPathFullDomain (n u) (inner u)}
        ((G u).induce (↑(bufferedPathFullDomain (n u) (inner u)):Set (Fin N))) (fA u))
      (partialFactorPhysicalEdgesPoly {x // x∈bufferedPathFullDomain (n v) (inner v)}
        ((G v).induce (↑(bufferedPathFullDomain (n v) (inner v)):Set (Fin N))) (fA v)))
    (hAC:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x // x∈bufferedPathFullDomain (n u) (inner u)}
        ((G u).induce (↑(bufferedPathFullDomain (n u) (inner u)):Set (Fin N))) (fA u))
      (partialFactorPhysicalEdgesPoly {x // x∉bufferedPathStrictInterior (n v) (inner v)}
        ((G v).induce {x | x∉bufferedPathStrictInterior (n v) (inner v)}) (fC v)))
    (hCC:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x // x∉bufferedPathStrictInterior (n u) (inner u)}
        ((G u).induce {x | x∉bufferedPathStrictInterior (n u) (inner u)}) (fC u))
      (partialFactorPhysicalEdgesPoly {x // x∉bufferedPathStrictInterior (n v) (inner v)}
        ((G v).induce {x | x∉bufferedPathStrictInterior (n v) (inner v)}) (fC v))) : HasFactorDecomposition H G := by
  obtain ⟨f,_,_,hgraph,hphysical⟩:=buffered_factor_family_completion I G H hG n ext inner hinner hwalk
    fA fC hA hC hend hdis hAA hAC hCC
  exact completed_two_factor_set_packing_gives_decomposition hEven H hH G hG f hgraph hphysical
end Oberwolfach
