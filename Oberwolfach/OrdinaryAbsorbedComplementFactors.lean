module

public import Oberwolfach.OrdinaryAbsorbedRemainderCompletion
public import Oberwolfach.OrdinaryComplementRemainderDecomposition

@[expose] public section
/-! Once the complement embeddings are fixed, an absorbing wheel
completion of their actual remainder finishes all prescribed factors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_absorbed_complement_factors {n q r:ℕ}
    (G P Fbad:SimpleGraph (Fin n)) (hG:G.IsRegularOfDegree (2*q)) (hr:0<r)
    (Fs:Fin q→SimpleGraph (Fin n)) (hF:∀u,(Fs u).IsRegularOfDegree 2)
    (C:∀u,Finset (Fs u).ConnectedComponent)
    (hsize:∀u (c:↥(C u)),Fintype.card c.val=r)
    (fC:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (hC:∀u x y,((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).Adj x y→G.Adj (fC u x) (fC u y))
    (hCC:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x:Fin n // (Fs u).connectedComponentMk x∉C u}
        ((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}) (fC u))
      (partialFactorPhysicalEdgesPoly {x:Fin n // (Fs v).connectedComponentMk x∉C v}
        ((Fs v).induce {x | (Fs v).connectedComponentMk x∉C v}) (fC v)))
    (Hbase:Fin n→Fin q→Prop) (A T:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))):
    let Q:=G\ordinaryEmbeddedComplements Fs C fC
    let H:=fun v u=>v∉Set.range (fC u)
    let R:=ordinaryHostResources Q H;
    A⊆R→T⊆R→
    HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=Fbad) (Hbase:=Hbase) (r:=r)) (R\(A∪T))→
    HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=Fbad) (Hbase:=Hbase) (r:=r)) (A∪T)→
    HasFactorDecomposition G Fs :=by
  intro Q H R hA hT hpack habs
  apply ordinary_complement_remainder_decomposition G hG hr Fs hF C hsize fC hC hCC
  exact ordinary_absorbed_remainder_completion P Fbad Q Hbase H r A T hA hT hpack habs
end Oberwolfach
