module

public import Oberwolfach.OrdinaryCompletionFactorDecomposition
public import Oberwolfach.OrdinaryReservedSpokeCardinality

@[expose] public section
/-! The ordinary completion's spoke set is the complement of the already
embedded factor complement; its exact count and avoidance are automatic. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_completion_factor_decomposition_from_complement {n q r:ℕ}
    (G Q:SimpleGraph (Fin n)) (H:Fin n→Fin q→Prop)
    (hG:G.IsRegularOfDegree (2*q)) (hQ:Q≤G) (hr:0<r)
    (hdec:HasOrdinaryWheelDecomposition Q H r)
    (F:Fin q→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (C:∀u,Finset (F u).ConnectedComponent)
    (hsize:∀u (c:↥(C u)),Fintype.card c.val=r)
    (fC:∀u,{x:Fin n // (F u).connectedComponentMk x∉C u}↪Fin n)
    (hC:∀u x y,((F u).induce {x | (F u).connectedComponentMk x∉C u}).Adj x y→
      G.Adj (fC u x) (fC u y) ∧ ¬Q.Adj (fC u x) (fC u y))
    (hspokes:∀u v,H v u↔v∉Set.range (fC u))
    (hCC:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x:Fin n // (F u).connectedComponentMk x∉C u}
        ((F u).induce {x | (F u).connectedComponentMk x∉C u}) (fC u))
      (partialFactorPhysicalEdgesPoly {x:Fin n // (F v).connectedComponentMk x∉C v}
        ((F v).induce {x | (F v).connectedComponentMk x∉C v}) (fC v))):
    HasFactorDecomposition G F :=by
  have hcounts:=fun u=>ordinary_reserved_spoke_cardinality (F u) (C u) (hsize u) (fC u) (fun v=>H v u) (hspokes u)
  exact ordinary_completion_factor_decomposition G Q H hG hQ hr hdec F hF C hsize
    (fun u=>(hcounts u).1) fC hC (fun u x=>(hcounts u).2 x) hCC
end Oberwolfach
