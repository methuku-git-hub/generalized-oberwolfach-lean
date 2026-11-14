module

public import Oberwolfach.PartialFactorWalkEdgeDisjointnessPoly

@[expose] public section
/-! Every completed factor edge comes from the reserved-domain or complement
map when the strict interior has no neighbour outside the reserved domain. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem completed_factor_physical_edges_subset_union
    {X Y:Type*} [DecidableEq X] (G:SimpleGraph X) (A D:Finset X) (hDA:D⊆A)
    (f:X→Y) (fA:{x // x∈A}→Y) (fC:{x // x∉D}→Y)
    (hA:∀x (hx:x∈A),f x=fA ⟨x,hx⟩)
    (hC:∀x (hx:x∉D),f x=fC ⟨x,hx⟩)
    (hneigh:∀x,x∈D→∀y,G.Adj x y→y∈A) :
    partialFactorPhysicalEdgesPoly X G f ⊆
      partialFactorPhysicalEdgesPoly {x // x∈A} (G.induce (↑A:Set X)) fA ∪
      partialFactorPhysicalEdgesPoly {x // x∉D} (G.induce {x | x∉D}) fC := by
  intro e he
  obtain ⟨x,y,hxy,rfl⟩:=he
  by_cases hx:x∈D
  · have hxA:=hDA hx
    have hyA:=hneigh x hx y hxy
    left
    refine ⟨⟨x,hxA⟩,⟨y,hyA⟩,hxy,?_⟩
    rw [hA x hxA,hA y hyA]
  · by_cases hy:y∈D
    · have hxA:=hneigh y hy x hxy.symm
      have hyA:=hDA hy
      left
      refine ⟨⟨x,hxA⟩,⟨y,hyA⟩,hxy,?_⟩
      rw [hA x hxA,hA y hyA]
    · right
      refine ⟨⟨x,hx⟩,⟨y,hy⟩,hxy,?_⟩
      rw [hC x hx,hC y hy]

theorem completed_factor_family_physical_edges_disjoint
    {U X Y:Type*} [DecidableEq X]
    (G:U→SimpleGraph X) (A D:U→Finset X) (hDA:∀u,D u⊆A u)
    (f:U→X→Y) (fA:∀u,{x // x∈A u}→Y) (fC:∀u,{x // x∉D u}→Y)
    (hA:∀u x (hx:x∈A u),f u x=fA u ⟨x,hx⟩)
    (hC:∀u x (hx:x∉D u),f u x=fC u ⟨x,hx⟩)
    (hneigh:∀u x,x∈D u→∀y,(G u).Adj x y→y∈A u)
    (hAA:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x // x∈A u} ((G u).induce (↑(A u):Set X)) (fA u))
      (partialFactorPhysicalEdgesPoly {x // x∈A v} ((G v).induce (↑(A v):Set X)) (fA v)))
    (hAC:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x // x∈A u} ((G u).induce (↑(A u):Set X)) (fA u))
      (partialFactorPhysicalEdgesPoly {x // x∉D v} ((G v).induce {x | x∉D v}) (fC v)))
    (hCC:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x // x∉D u} ((G u).induce {x | x∉D u}) (fC u))
      (partialFactorPhysicalEdgesPoly {x // x∉D v} ((G v).induce {x | x∉D v}) (fC v))) :
    ∀u v,u≠v→Disjoint (partialFactorPhysicalEdgesPoly X (G u) (f u))
      (partialFactorPhysicalEdgesPoly X (G v) (f v)) := by
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
