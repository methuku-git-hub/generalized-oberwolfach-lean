module

public import Oberwolfach.OrdinaryCompletionFromComplement

@[expose] public section
/-! The natural remainder after embedding all unreserved components has
exactly the rims and spokes needed to finish the factors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinaryEmbeddedComplements {n q:ℕ}
    (F:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (F u).ConnectedComponent)
    (fC:∀u,{x:Fin n // (F u).connectedComponentMk x∉C u}↪Fin n):SimpleGraph (Fin n) :=
  ⨆u,((F u).induce {x | (F u).connectedComponentMk x∉C u}).map (fC u)

theorem ordinary_complement_remainder_decomposition {n q r:ℕ}
    (G:SimpleGraph (Fin n)) (hG:G.IsRegularOfDegree (2*q)) (hr:0<r)
    (F:Fin q→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (C:∀u,Finset (F u).ConnectedComponent)
    (hsize:∀u (c:↥(C u)),Fintype.card c.val=r)
    (fC:∀u,{x:Fin n // (F u).connectedComponentMk x∉C u}↪Fin n)
    (hC:∀u x y,((F u).induce {x | (F u).connectedComponentMk x∉C u}).Adj x y→G.Adj (fC u x) (fC u y))
    (hCC:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x:Fin n // (F u).connectedComponentMk x∉C u}
        ((F u).induce {x | (F u).connectedComponentMk x∉C u}) (fC u))
      (partialFactorPhysicalEdgesPoly {x:Fin n // (F v).connectedComponentMk x∉C v}
        ((F v).induce {x | (F v).connectedComponentMk x∉C v}) (fC v)))
    (hdec:HasOrdinaryWheelDecomposition (G \ ordinaryEmbeddedComplements F C fC)
      (fun v u=>v∉Set.range (fC u)) r):
    HasFactorDecomposition G F :=by
  let Q:=G \ ordinaryEmbeddedComplements F C fC
  have hQ:Q≤G:=by intro x y h;exact h.1
  apply ordinary_completion_factor_decomposition_from_complement G Q (fun v u=>v∉Set.range (fC u))
    hG hQ hr hdec F hF C hsize fC
  · intro u x y hxy
    refine ⟨hC u x y hxy,?_⟩
    intro hh
    have hin:((F u).induce {x | (F u).connectedComponentMk x∉C u}).map (fC u)≤ordinaryEmbeddedComplements F C fC:=
      le_iSup (fun u=>((F u).induce {x | (F u).connectedComponentMk x∉C u}).map (fC u)) u
    have hmem:(ordinaryEmbeddedComplements F C fC).Adj (fC u x) (fC u y):=
      hin (SimpleGraph.map_adj_apply.mpr hxy)
    exact hh.2 hmem
  · intro u v
    rfl
  · exact hCC
end Oberwolfach
