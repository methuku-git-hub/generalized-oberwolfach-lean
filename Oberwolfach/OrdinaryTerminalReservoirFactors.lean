module

public import Oberwolfach.OrdinaryAllTerminalSampleEvent
public import Oberwolfach.OrdinaryAbsorbedComplementFactors

@[expose] public section
/-! If the complement packing leaves a covered outer remainder and an
admissible terminal remainder, the fixed terminal reservoir completes the
original factors. All packing and containment premises remain explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_terminal_reservoir_completes_factors {n q r m:ℕ}
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
    (Hbase:Fin n→Fin q→Prop) (Wterm:Finset (Fin n)) (Bterm:Finset (Fin q))
    (A:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (Gterm:SimpleGraph (Fin n)) (Hterm:Fin n→Fin q→Prop)
    (hroot:ordinaryHostResources Gterm Hterm⊆ordinaryRootResources Wterm Bterm)
    (hsmall:(ordinaryPhysicalGraph Gterm Hterm).support.toFinset.card≤m)
    (hbal:∀v,Gterm.degree v=2*(Finset.univ.filter (Hterm v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>Hterm v u)).card)
    (htermG:Gterm≤P) (htermH:∀v u,Hterm v u→Hbase v u)
    (hres:∀(G':SimpleGraph (Fin n)) (H':Fin n→Fin q→Prop),
      ordinaryHostResources G' H'⊆ordinaryRootResources Wterm Bterm →
      (ordinaryPhysicalGraph G' H').support.toFinset.card≤m →
      (∀v,G'.degree v=2*(Finset.univ.filter (H' v)).card) →
      (∀u,r∣(Finset.univ.filter (fun v=>H' v u)).card) →
      G'≤P → (∀v u,H' v u→Hbase v u) →
      IsResourceAbsorber (ordinaryWheelResources (P:=P) (F:=Fbad) (Hbase:=Hbase) (r:=r))
        (ordinaryHostResources G' H') A):
    let Q:=G\ordinaryEmbeddedComplements Fs C fC
    let H:=fun v u=>v∉Set.range (fC u)
    let R:=ordinaryHostResources Q H
    let T:=ordinaryHostResources Gterm Hterm;
    A⊆R → T⊆R →
    HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=Fbad) (Hbase:=Hbase) (r:=r))
      (R\(A∪T)) → HasFactorDecomposition G Fs:=by
  intro Q H R T hA hT hpack
  apply ordinary_absorbed_complement_factors G P Fbad hG hr Fs hF C hsize fC hC hCC Hbase A T hA hT hpack
  exact (hres Gterm Hterm hroot hsmall hbal hdiv htermG htermH).2.2
end Oberwolfach
