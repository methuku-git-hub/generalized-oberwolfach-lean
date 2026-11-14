module

public import Oberwolfach.OrdinaryTraceCoverDownCompletion

@[expose] public section
/-! A reusable ordinary wheel witness: a protected absorber and the
    first and later cover-downs for one common trace. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def OrdinaryWheelTraceWitness
    (Q P F:SimpleGraph V) (H Hbase:V→U→Prop) (r:ℕ):Prop :=
  ∃(m:ℕ) (Wterm:Finset V) (Bterm:Finset U)
    (A:Finset (Sym2 V⊕(V×U))) (L:ℕ)
    (X T:ℕ→Finset V) (Z W:ℕ→Finset U) (cost deepCost:ℕ→ℝ),
    Wterm.card+Bterm.card≤m ∧ 0<L ∧ X (L-1)=Wterm ∧ Z (L-1)=Bterm ∧
    Q≤P ∧ (∀v u,H v u→Hbase v u) ∧
    A⊆ordinaryHostResources Q H ∧
    HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r)) A ∧
    (∀(G':SimpleGraph V) (H':V→U→Prop),
      ordinaryHostResources G' H'⊆ordinaryRootResources Wterm Bterm →
      (ordinaryPhysicalGraph G' H').support.toFinset.card≤m →
      (∀v,G'.degree v=2*(Finset.univ.filter (H' v)).card) →
      (∀u,r∣(Finset.univ.filter (fun v=>H' v u)).card) →
      G'≤P → (∀v u,H' v u→Hbase v u) →
      IsResourceAbsorber (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r))
        (ordinaryHostResources G' H') A) ∧
    let Q₀:=Q\ordinaryResourceRim Q A
    let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈A);
    OrdinaryProtectedHostCoverDownResult Q₀ F H₀ (X 0) (T 0) (Z 0) (W 0) r (cost 0) (deepCost 0) ∧
    (∀i,X (i+1)⊆X i) ∧ (∀i,T (i+1)⊆X i) ∧ (∀i,Z (i+1)⊆Z i) ∧ (∀i,W (i+1)⊆Z i) ∧
    (∀i,0≤cost i) ∧ (∀i,0≤deepCost i) ∧
    (∀i,i+1<L→∀S (G:SimpleGraph V) (Hs:V→U→Prop),
      OrdinaryProtectedTrace Q₀ H₀ X T Z W cost deepCost (i+1) S→
      ordinaryHostResources G Hs=S→
      (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
      (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card)→
      OrdinaryProtectedHostCoverDownResult (G.induce ((X i):Set V)) (F.induce ((X i):Set V))
        (fun (v:↥(X i)) (u:↥(Z i))=>Hs v.val u.val)
        (ordinaryContainedTarget (X i) (X (i+1))) (ordinaryContainedTarget (X i) (T (i+1)))
        (ordinaryContainedTarget (Z i) (Z (i+1))) (ordinaryContainedTarget (Z i) (W (i+1))) r
        (cost (i+1)) (deepCost (i+1)))

theorem ordinary_wheel_trace_witness_completion
    (Q P F:SimpleGraph V) (H Hbase:V→U→Prop) (r:ℕ)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (h:OrdinaryWheelTraceWitness Q P F H Hbase r):
    HasOrdinaryWheelDecomposition Q H r :=by
  obtain ⟨m,Wterm,Bterm,A,L,X,T,Z,W,cost,deepCost,hsize,hL,hW,hB,hQP,hHbase,hA,hdecA,hres,hfirst,hXX,hTX,hZZ,hWZ,hcost,hdeep,hlocal⟩:=h
  exact ordinary_trace_coverdown_completion Q P F H Hbase r m Wterm Bterm hsize hbal hdiv hQP hHbase
    A hA hdecA hres L hL X T Z W cost deepCost hW hB hfirst hXX hTX hZZ hWZ hcost hdeep hlocal
end Oberwolfach
