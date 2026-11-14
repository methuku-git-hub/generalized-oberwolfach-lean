module

public import Oberwolfach.PartialEmbeddingPhysicalEdgeUnion

@[expose] public section
/-! Physical-edge disjointness survives completion for a family whose source
type is allowed to depend on the factor. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem completed_dependent_factor_family_physical_edges_disjoint
    {U Y:Type*} {X:U→Type*} [∀u,DecidableEq (X u)]
    (G:∀u,SimpleGraph (X u)) (A D:∀u,Finset (X u)) (hDA:∀u,D u⊆A u)
    (f:∀u,X u→Y) (fA:∀u,{x // x∈A u}→Y) (fC:∀u,{x // x∉D u}→Y)
    (hA:∀u x (hx:x∈A u),f u x=fA u ⟨x,hx⟩)
    (hC:∀u x (hx:x∉D u),f u x=fC u ⟨x,hx⟩)
    (hneigh:∀u x,x∈D u→∀y,(G u).Adj x y→y∈A u)
    (hAA:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x // x∈A u} ((G u).induce (↑(A u):Set (X u))) (fA u))
      (partialFactorPhysicalEdgesPoly {x // x∈A v} ((G v).induce (↑(A v):Set (X v))) (fA v)))
    (hAC:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x // x∈A u} ((G u).induce (↑(A u):Set (X u))) (fA u))
      (partialFactorPhysicalEdgesPoly {x // x∉D v} ((G v).induce {x | x∉D v}) (fC v)))
    (hCC:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x // x∉D u} ((G u).induce {x | x∉D u}) (fC u))
      (partialFactorPhysicalEdgesPoly {x // x∉D v} ((G v).induce {x | x∉D v}) (fC v))):
    ∀u v,u≠v→Disjoint (partialFactorPhysicalEdgesPoly (X u) (G u) (f u))
      (partialFactorPhysicalEdgesPoly (X v) (G v) (f v)):=by
  intro u v huv
  apply Set.disjoint_left.mpr
  intro e heu hev
  have hu:=completed_factor_physical_edges_subset_union (G u) (A u) (D u) (hDA u) (f u) (fA u) (fC u) (hA u) (hC u) (hneigh u) heu
  have hv:=completed_factor_physical_edges_subset_union (G v) (A v) (D v) (hDA v) (f v) (fA v) (fC v) (hA v) (hC v) (hneigh v) hev
  rcases hu with hu|hu <;> rcases hv with hv|hv
  · exact (Set.disjoint_left.mp (hAA u v huv)) hu hv
  · exact (Set.disjoint_left.mp (hAC u v huv)) hu hv
  · exact (Set.disjoint_left.mp (hAC v u (Ne.symm huv))) hv hu
  · exact (Set.disjoint_left.mp (hCC u v huv)) hu hv
end Oberwolfach
