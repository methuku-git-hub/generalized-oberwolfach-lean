module

public import Oberwolfach.FullFactorSetPackingToDecomposition

@[expose] public section
/-! Disjoint physical edge sets of embedded factor complements give disjoint
actual mapped graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_complement_piece_disjoint {n q:ℕ}
    (F:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (F u).ConnectedComponent)
    (fC:∀u,{x:Fin n // (F u).connectedComponentMk x∉C u}↪Fin n)
    (hCC:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x:Fin n // (F u).connectedComponentMk x∉C u}
        ((F u).induce {x | (F u).connectedComponentMk x∉C u}) (fC u))
      (partialFactorPhysicalEdgesPoly {x:Fin n // (F v).connectedComponentMk x∉C v}
        ((F v).induce {x | (F v).connectedComponentMk x∉C v}) (fC v))):
    ∀u v,u≠v→Disjoint
      (((F u).induce {x | (F u).connectedComponentMk x∉C u}).map (fC u)).edgeFinset
      (((F v).induce {x | (F v).connectedComponentMk x∉C v}).map (fC v)).edgeFinset :=by
  intro u v huv
  apply Finset.disjoint_left.mpr
  intro e heu hev
  have hU:e∈partialFactorPhysicalEdgesPoly {x:Fin n // (F u).connectedComponentMk x∉C u}
      ((F u).induce {x | (F u).connectedComponentMk x∉C u}) (fC u):=by
    have he:e∈(((F u).induce {x | (F u).connectedComponentMk x∉C u}).edgeFinset).image (Sym2.map (fC u)):=by
      rw [SimpleGraph.edgeFinset_map,Finset.map_eq_image] at heu
      have heq:⇑(fC u).sym2Map=Sym2.map (fC u):=by
        funext z;exact Function.Embedding.sym2Map_apply (fC u) z
      rwa [heq] at heu
    exact mapped_edge_finset_mem_physical_set _ _ e he
  have hV:e∈partialFactorPhysicalEdgesPoly {x:Fin n // (F v).connectedComponentMk x∉C v}
      ((F v).induce {x | (F v).connectedComponentMk x∉C v}) (fC v):=by
    have he:e∈(((F v).induce {x | (F v).connectedComponentMk x∉C v}).edgeFinset).image (Sym2.map (fC v)):=by
      rw [SimpleGraph.edgeFinset_map,Finset.map_eq_image] at hev
      have heq:⇑(fC v).sym2Map=Sym2.map (fC v):=by
        funext z;exact Function.Embedding.sym2Map_apply (fC v) z
      rwa [heq] at hev
    exact mapped_edge_finset_mem_physical_set _ _ e he
  exact Set.disjoint_left.mp (hCC u v huv) hU hV
end Oberwolfach
