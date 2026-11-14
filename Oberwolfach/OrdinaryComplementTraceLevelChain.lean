module

public import Oberwolfach.OrdinaryTraceCoverDownCompletion
public import Oberwolfach.OrdinaryComplementRemainderBalance
public import Oberwolfach.OrdinaryComplementRemainderDecomposition

@[expose] public section
/-! The actual embedded-complement remainder supplies the balance and
    divisibility needed by the protected ordinary wheel trace. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_complement_trace_level_chain
    {n q r m:ℕ}
    (S P Fbad:SimpleGraph (Fin n)) (hS:S.IsRegularOfDegree (2*q)) (hSP:S≤P) (hr:0<r)
    (Fs:Fin q→SimpleGraph (Fin n)) (hF:∀u,(Fs u).IsRegularOfDegree 2)
    (C:∀u,Finset (Fs u).ConnectedComponent)
    (hComponent:∀u (c:↥(C u)),Fintype.card c.val=r)
    (fC:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (hC:∀u x y,((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).Adj x y→S.Adj (fC u x) (fC u y))
    (hCC:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x:Fin n // (Fs u).connectedComponentMk x∉C u}
        ((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}) (fC u))
      (partialFactorPhysicalEdgesPoly {x:Fin n // (Fs v).connectedComponentMk x∉C v}
        ((Fs v).induce {x | (Fs v).connectedComponentMk x∉C v}) (fC v)))
    (Hbase:Fin n→Fin q→Prop) (Wterm:Finset (Fin n)) (Bterm:Finset (Fin q))
    (hsize:Wterm.card+Bterm.card≤m)
    (A:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (L:ℕ) (hL:0<L) (X T:ℕ→Finset (Fin n)) (Z W:ℕ→Finset (Fin q)) (cost deepCost:ℕ→ℝ)
    (hW:X (L-1)=Wterm) (hB:Z (L-1)=Bterm):
    let Q:=S\ordinaryEmbeddedComplements Fs C fC
    let H:=fun v u=>v∉Set.range (fC u)
    let Q₀:=Q\ordinaryResourceRim Q A
    let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈A);
    (∀v u,H v u→Hbase v u) →
    A⊆ordinaryHostResources Q H →
    HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=Fbad) (Hbase:=Hbase) (r:=r)) A →
    (∀(G':SimpleGraph (Fin n)) (H':Fin n→Fin q→Prop),
      ordinaryHostResources G' H'⊆ordinaryRootResources Wterm Bterm →
      (ordinaryPhysicalGraph G' H').support.toFinset.card≤m →
      (∀v,G'.degree v=2*(Finset.univ.filter (H' v)).card) →
      (∀u,r∣(Finset.univ.filter (fun v=>H' v u)).card) →
      G'≤P → (∀v u,H' v u→Hbase v u) →
      IsResourceAbsorber (ordinaryWheelResources (P:=P) (F:=Fbad) (Hbase:=Hbase) (r:=r))
        (ordinaryHostResources G' H') A) →
    OrdinaryProtectedHostCoverDownResult Q₀ Fbad H₀ (X 0) (T 0) (Z 0) (W 0) r (cost 0) (deepCost 0)→
    (∀i,X (i+1)⊆X i)→(∀i,T (i+1)⊆X i)→(∀i,Z (i+1)⊆Z i)→(∀i,W (i+1)⊆Z i)→
    (∀i,0≤cost i)→(∀i,0≤deepCost i)→
    (∀i,i+1<L→∀R (G:SimpleGraph (Fin n)) (Hs:Fin n→Fin q→Prop),
      OrdinaryProtectedTrace Q₀ H₀ X T Z W cost deepCost (i+1) R→
      ordinaryHostResources G Hs=R→
      (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
      (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card)→
      OrdinaryProtectedHostCoverDownResult (G.induce ((X i):Set (Fin n))) (Fbad.induce ((X i):Set (Fin n)))
        (fun (v:↥(X i)) (u:↥(Z i))=>Hs v.val u.val)
        (ordinaryContainedTarget (X i) (X (i+1))) (ordinaryContainedTarget (X i) (T (i+1)))
        (ordinaryContainedTarget (Z i) (Z (i+1))) (ordinaryContainedTarget (Z i) (W (i+1))) r
        (cost (i+1)) (deepCost (i+1)))→
    HasOrdinaryWheelDecomposition Q H r ∧ HasFactorDecomposition S Fs :=by
  intro Q H Q₀ H₀ hHbase hA hdecA hres hfirst hXX hTX hZZ hWZ hcost hdeep hlocal
  obtain ⟨hbal,hdiv⟩:=ordinary_complement_remainder_balance S hS Fs hF C hComponent fC hC hCC
  have hbal':∀v,Q.degree v=2*(Finset.univ.filter (H v)).card:=by
    intro v
    have hh:=hbal v
    convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _
  have hdiv':∀u,r∣(Finset.univ.filter (fun v=>H v u)).card:=by
    intro u
    have hh:=hdiv u
    convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _
  have hQP:Q≤P:=(show Q≤S from sdiff_le).trans hSP
  have hWheel:HasOrdinaryWheelDecomposition Q H r:=
    ordinary_trace_coverdown_completion Q P Fbad H Hbase r m Wterm Bterm hsize
      (by intro v; have hh:=hbal' v; convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _)
      (by intro u; have hh:=hdiv' u; convert hh using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _)
      hQP hHbase A hA hdecA hres L hL X T Z W cost deepCost hW hB hfirst hXX hTX hZZ hWZ hcost hdeep hlocal
  exact ⟨hWheel,ordinary_complement_remainder_decomposition S hS hr Fs hF C hComponent fC hC hCC hWheel⟩
end Oberwolfach
