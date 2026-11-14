module

public import Oberwolfach.OrdinaryTerminalRemainderBalance
public import Oberwolfach.OrdinaryComplementRemainderBalance

@[expose] public section
/-! The actual remainder after embedded complements and any further
contained wheel packing remains balanced and divisible. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_complement_terminal_balance {n q r:ℕ}
    (G P Fbad:SimpleGraph (Fin n)) (hG:G.IsRegularOfDegree (2*q))
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
    (Hbase:Fin n→Fin q→Prop) (K:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))):
    let Q:=G\ordinaryEmbeddedComplements Fs C fC
    let H:=fun v u=>v∉Set.range (fC u);
    K⊆ordinaryHostResources Q H →
    HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=Fbad) (Hbase:=Hbase) (r:=r)) K →
    ∃(Gterm:SimpleGraph (Fin n)) (Hterm:Fin n→Fin q→Prop),
      ordinaryHostResources Gterm Hterm=ordinaryHostResources Q H\K ∧
      (∀v,Gterm.degree v=2*(Finset.univ.filter (Hterm v)).card) ∧
      (∀u,r∣(Finset.univ.filter (fun v=>Hterm v u)).card) ∧
      Gterm≤Q ∧ (∀v u,Hterm v u→H v u):=by
  intro Q H hK hdec
  obtain ⟨hb,hd⟩:=ordinary_complement_remainder_balance G hG Fs hF C hsize fC hC hCC
  apply ordinary_resource_terminal_remainder_balance Q P Fbad H Hbase r
  · intro v
    have hh:=hb v
    convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _
  · intro u
    have hh:=hd u
    convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _
  · exact hK
  · exact hdec
end Oberwolfach
