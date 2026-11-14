module

public import Oberwolfach.BufferedPathWalkFullMatch
public import Oberwolfach.DependentPartialEmbeddingPhysicalEdges

@[expose] public section
/-! Complete all factors while preserving the reserved and complement maps,
then transfer their three pairwise physical-edge disjointness conditions. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_dependent_factor_family_completion
    {U Y:Type*} {X:U→Type*} [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    (I:U→Type*) [∀u,Fintype (I u)]
    (G:∀u,SimpleGraph (X u)) (H:SimpleGraph Y) (hG:∀u,(G u).IsRegularOfDegree 2)
    (n:∀u,I u→ℕ)
    (ext:∀u (i:I u),Fin (n u i+5)↪X u) (inner:∀u (i:I u),Fin (n u i+1)↪X u)
    (hinner:∀u i p,inner u i p=ext u i ⟨p.val+2,by omega⟩)
    (hwalk:∀u i,∃p:(G u).Walk (ext u i ⟨0,by omega⟩) (ext u i ⟨n u i+4,by omega⟩),
      p.length=n u i+4 ∧ p.support=List.ofFn (ext u i))
    (fA:∀u,{x // x∈bufferedPathFullDomain (n u) (inner u)}↪Y)
    (fC:∀u,{x // x∉bufferedPathStrictInterior (n u) (inner u)}↪Y)
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
        ((G u).induce (↑(bufferedPathFullDomain (n u) (inner u)):Set (X u))) (fA u))
      (partialFactorPhysicalEdgesPoly {x // x∈bufferedPathFullDomain (n v) (inner v)}
        ((G v).induce (↑(bufferedPathFullDomain (n v) (inner v)):Set (X v))) (fA v)))
    (hAC:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x // x∈bufferedPathFullDomain (n u) (inner u)}
        ((G u).induce (↑(bufferedPathFullDomain (n u) (inner u)):Set (X u))) (fA u))
      (partialFactorPhysicalEdgesPoly {x // x∉bufferedPathStrictInterior (n v) (inner v)}
        ((G v).induce {x | x∉bufferedPathStrictInterior (n v) (inner v)}) (fC v)))
    (hCC:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x // x∉bufferedPathStrictInterior (n u) (inner u)}
        ((G u).induce {x | x∉bufferedPathStrictInterior (n u) (inner u)}) (fC u))
      (partialFactorPhysicalEdgesPoly {x // x∉bufferedPathStrictInterior (n v) (inner v)}
        ((G v).induce {x | x∉bufferedPathStrictInterior (n v) (inner v)}) (fC v))) :
    ∃f:∀u,X u↪Y,
      (∀u x (hx:x∈bufferedPathFullDomain (n u) (inner u)),f u x=fA u ⟨x,hx⟩) ∧
      (∀u x (hx:x∉bufferedPathStrictInterior (n u) (inner u)),f u x=fC u ⟨x,hx⟩) ∧
      (∀u x y,(G u).Adj x y→H.Adj (f u x) (f u y)) ∧
      (∀u v,u≠v→Disjoint (partialFactorPhysicalEdgesPoly (X u) (G u) (f u))
        (partialFactorPhysicalEdgesPoly (X v) (G v) (f v))) := by
  classical
  have hex:∀u,∃g:X u↪Y,
      (∀x (hx:x∈bufferedPathFullDomain (n u) (inner u)),g x=fA u ⟨x,hx⟩) ∧
      (∀x (hx:x∉bufferedPathStrictInterior (n u) (inner u)),g x=fC u ⟨x,hx⟩) ∧
      (∀x y,(G u).Adj x y→H.Adj (g x) (g y)):=by
    intro u
    exact buffered_walk_embeddings_complete_preserving_both_maps (G u) H (hG u) (n u)
      (ext u) (inner u) (hinner u) (hwalk u) (fA u) (fC u) (hA u) (hC u) (hend u) (hdis u)
  let f:∀u,X u↪Y:=fun u=>Classical.choose (hex u)
  have hf:∀u,(∀x (hx:x∈bufferedPathFullDomain (n u) (inner u)),f u x=fA u ⟨x,hx⟩) ∧
      (∀x (hx:x∉bufferedPathStrictInterior (n u) (inner u)),f u x=fC u ⟨x,hx⟩) ∧
      (∀x y,(G u).Adj x y→H.Adj (f u x) (f u y)):=fun u=>Classical.choose_spec (hex u)
  refine ⟨f,fun u=>(hf u).1,fun u=>(hf u).2.1,fun u=>(hf u).2.2,?_⟩
  apply completed_dependent_factor_family_physical_edges_disjoint G
    (fun u=>bufferedPathFullDomain (n u) (inner u))
    (fun u=>bufferedPathStrictInterior (n u) (inner u))
    (fun u=>buffered_strict_interior_subset_domain (n u) (inner u))
    (fun u=>f u) (fun u=>fA u) (fun u=>fC u)
    (fun u=>(hf u).1) (fun u=>(hf u).2.1) ?_ hAA hAC hCC
  intro u
  have hstep:∀i (p:Fin (n u i+4)),(G u).Adj (ext u i ⟨p.val,by omega⟩) (ext u i ⟨p.val+1,by omega⟩):=by
    intro i p
    obtain ⟨walk,hlen,hsupport⟩:=hwalk u i
    exact walk_ofFn_support_adjacent (G u) (n u i+4) (ext u i) walk hlen hsupport p
  exact buffered_strict_interior_neighborhood (G u) (hG u) (n u) (ext u) (inner u) (hinner u) hstep
end Oberwolfach
