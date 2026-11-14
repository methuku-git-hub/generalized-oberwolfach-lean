module

public import Oberwolfach.PhysicalSetFinsetEquivalence
public import Oberwolfach.ResidualActualEdgePartition

@[expose] public section
/-! The exact old/residual edge partition reduces whole-factor host containment
and pairwise disjointness to the corresponding physical edge-set conditions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem dependent_glued_factor_host_and_disjoint
    {U V:Type} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    {X:U→Type} [∀u,Fintype (X u)] [∀u,DecidableEq (X u)]
    (F:∀u,SimpleGraph (X u)) (P:SimpleGraph V) (f:∀u,X u→V)
    (Old New:U→Finset (Sym2 V))
    (hpart:∀u,((F u).edgeFinset).image (Sym2.map (f u))=Old u∪New u)
    (hOldHost:∀u,Old u⊆P.edgeFinset) (hNewHost:∀u,New u⊆P.edgeFinset)
    (hOO:∀u v,u≠v→Disjoint (Old u) (Old v))
    (hON:∀u v,Disjoint (Old u) (New v))
    (hNN:∀u v,u≠v→Disjoint (New u) (New v)):
    (∀u x y,(F u).Adj x y→P.Adj (f u x) (f u y)) ∧
    (∀u v,u≠v→Disjoint (partialFactorPhysicalEdgesPoly (X u) (F u) (f u))
      (partialFactorPhysicalEdgesPoly (X v) (F v) (f v))):=by
  constructor
  · intro u x y hxy
    have he:s(f u x,f u y)∈((F u).edgeFinset).image (Sym2.map (f u)):=by
      exact Finset.mem_image.mpr ⟨s(x,y),SimpleGraph.mem_edgeFinset.mpr hxy,rfl⟩
    rw [hpart u] at he
    have hh:s(f u x,f u y)∈P.edgeFinset:=by
      rcases Finset.mem_union.mp he with he|he
      · exact hOldHost u he
      · exact hNewHost u he
    simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hh
  · intro u v huv
    apply partial_factor_sets_disjoint_of_edge_finsets
    rw [hpart u,hpart v]
    apply Finset.disjoint_union_left.mpr
    constructor
    · apply Finset.disjoint_union_right.mpr
      exact ⟨hOO u v huv,hON u v⟩
    · apply Finset.disjoint_union_right.mpr
      exact ⟨(hON v u).symm,hNN u v huv⟩
end Oberwolfach
