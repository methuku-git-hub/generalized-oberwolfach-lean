module

public import Oberwolfach.OrdinaryCoveredRemainderCompletion
public import Oberwolfach.OrdinaryComplementRemainderBalance
public import Oberwolfach.OrdinaryComplementRemainderDecomposition

@[expose] public section
/-! Glue the actual complement embedding to a universal terminal reservoir
and an ordinary wheel packing covering everything outside the terminal pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_covered_complement_factors {n q r m:ℕ}
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
    (Hbase:Fin n→Fin q→Prop) (W:Finset (Fin n)) (B:Finset (Fin q)) (hm:W.card+B.card≤m)
    (A D:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (hres:∀(G':SimpleGraph (Fin n)) (H':Fin n→Fin q→Prop),
      ordinaryHostResources G' H'⊆ordinaryRootResources W B →
      (ordinaryPhysicalGraph G' H').support.toFinset.card≤m →
      (∀v,G'.degree v=2*(Finset.univ.filter (H' v)).card) →
      (∀u,r∣(Finset.univ.filter (fun v=>H' v u)).card) →
      G'≤P → (∀v u,H' v u→Hbase v u) →
      IsResourceAbsorber (ordinaryWheelResources (P:=P) (F:=Fbad) (Hbase:=Hbase) (r:=r))
        (ordinaryHostResources G' H') A):
    let Q:=G\ordinaryEmbeddedComplements Fs C fC
    let H:=fun v u=>v∉Set.range (fC u)
    let Host:=ordinaryHostResources Q H;
    (∀v∈W,∀w∈W,Q.Adj v w→P.Adj v w) →
    (∀v∈W,∀u∈B,H v u→Hbase v u) →
    A⊆Host → D⊆Host → Disjoint A D →
    HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=Fbad) (Hbase:=Hbase) (r:=r)) A →
    HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=Fbad) (Hbase:=Hbase) (r:=r)) D →
    Host\(A∪D)⊆ordinaryRootResources W B → HasFactorDecomposition G Fs:=by
  intro Q H Host hP hH hA hD hdis hdecA hdecD hroot
  obtain ⟨hb,hd⟩:=ordinary_complement_remainder_balance G hG Fs hF C hsize fC hC hCC
  have hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card:=by
    intro v
    have hh:=hb v
    convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _
  have hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card:=by
    intro u
    have hh:=hd u
    convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _
  have hcomplete:=ordinary_covered_remainder_completion Q P Fbad H Hbase r m W B hm
    (by
      intro v
      have hh:=hbal v
      convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _) (by
      intro u
      have hh:=hdiv u
      convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _)
    hP hH A D hA hD hdis hdecA hdecD hroot hres
  exact ordinary_complement_remainder_decomposition G hG hr Fs hF C hsize fC hC hCC hcomplete
end Oberwolfach
