module

public import Oberwolfach.OrdinaryCompletionFactorEmbeddings
public import Oberwolfach.FullFactorSetPackingToDecomposition

@[expose] public section
/-! Complete the actual ordinary wheel decomposition and the disjoint
complement embeddings into a decomposition of the regular class graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_completion_factor_decomposition {n q r:ℕ}
    (G Q:SimpleGraph (Fin n)) (H:Fin n→Fin q→Prop)
    (hG:G.IsRegularOfDegree (2*q)) (hQ:Q≤G) (hr:0<r)
    (hdec:HasOrdinaryWheelDecomposition Q H r)
    (F:Fin q→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (C:∀u,Finset (F u).ConnectedComponent)
    (hsize:∀u (c:↥(C u)),Fintype.card c.val=r)
    (hspokes:∀u,(Finset.univ.filter (fun v=>H v u)).card=r*(C u).card)
    (fC:∀u,{x:Fin n // (F u).connectedComponentMk x∉C u}↪Fin n)
    (hC:∀u x y,((F u).induce {x | (F u).connectedComponentMk x∉C u}).Adj x y→
      G.Adj (fC u x) (fC u y) ∧ ¬Q.Adj (fC u x) (fC u y))
    (havoid:∀u (x:{x:Fin n // (F u).connectedComponentMk x∉C u}),¬H (fC u x) u)
    (hCC:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x:Fin n // (F u).connectedComponentMk x∉C u}
        ((F u).induce {x | (F u).connectedComponentMk x∉C u}) (fC u))
      (partialFactorPhysicalEdgesPoly {x:Fin n // (F v).connectedComponentMk x∉C v}
        ((F v).induce {x | (F v).connectedComponentMk x∉C v}) (fC v))):
    HasFactorDecomposition G F :=by
  obtain ⟨f,_,hgraph,hdis⟩:=ordinary_completion_factor_embeddings G Q H hQ hr hdec F hF C hsize hspokes fC hC havoid hCC
  apply spanning_two_factor_embeddings_give_decomposition G hG F hF (fun u=>f u) (fun u=>(f u).injective)
  · intro u e he
    obtain ⟨x,y,hxy,heq⟩:=mapped_edge_finset_mem_physical_set (F u) (f u) e he
    rw [heq]
    exact SimpleGraph.mem_edgeFinset.mpr (hgraph u x y hxy)
  · intro u v huv
    apply Finset.disjoint_left.mpr
    intro e heu hev
    exact Set.disjoint_left.mp (hdis u v huv)
      (mapped_edge_finset_mem_physical_set (F u) (f u) e heu)
      (mapped_edge_finset_mem_physical_set (F v) (f v) e hev)
end Oberwolfach
