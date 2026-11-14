module

public import Oberwolfach.OrdinaryTraceCoverDownCases
public import Oberwolfach.OrdinaryProtectedTraceLevelChain

@[expose] public section
/-! A first ambient cover-down, induced cover-downs at later levels, and a
terminal absorber complete the original host decomposition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_trace_coverdown_completion
    (Q P F:SimpleGraph V) (H Hbase:V→U→Prop) (r m:ℕ)
    (Wterm:Finset V) (Bterm:Finset U) (hsize:Wterm.card+Bterm.card≤m)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (hQP:Q≤P) (hHbase:∀v u,H v u→Hbase v u)
    (A:Finset (Sym2 V⊕(V×U))) (hA:A⊆ordinaryHostResources Q H)
    (hdecA:HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r)) A)
    (hres:∀(G':SimpleGraph V) (H':V→U→Prop),
      ordinaryHostResources G' H'⊆ordinaryRootResources Wterm Bterm →
      (ordinaryPhysicalGraph G' H').support.toFinset.card≤m →
      (∀v,G'.degree v=2*(Finset.univ.filter (H' v)).card) →
      (∀u,r∣(Finset.univ.filter (fun v=>H' v u)).card) →
      G'≤P → (∀v u,H' v u→Hbase v u) →
      IsResourceAbsorber (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r))
        (ordinaryHostResources G' H') A)
    (L:ℕ) (hL:0<L) (X T:ℕ→Finset V) (Z W:ℕ→Finset U) (cost deepCost:ℕ→ℝ)
    (hW:X (L-1)=Wterm) (hB:Z (L-1)=Bterm):
    let Q₀:=Q\ordinaryResourceRim Q A;
    let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈A);
    OrdinaryProtectedHostCoverDownResult Q₀ F H₀ (X 0) (T 0) (Z 0) (W 0) r (cost 0) (deepCost 0)→
    (∀i,X (i+1)⊆X i)→(∀i,T (i+1)⊆X i)→(∀i,Z (i+1)⊆Z i)→(∀i,W (i+1)⊆Z i)→
    (∀i,0≤cost i)→(∀i,0≤deepCost i)→
    (∀i,i+1<L→∀S (G:SimpleGraph V) (Hs:V→U→Prop),
      OrdinaryProtectedTrace Q₀ H₀ X T Z W cost deepCost (i+1) S→
      ordinaryHostResources G Hs=S→
      (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
      (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card)→
      OrdinaryProtectedHostCoverDownResult (G.induce ((X i):Set V)) (F.induce ((X i):Set V))
        (fun (v:↥(X i)) (u:↥(Z i))=>Hs v.val u.val)
        (ordinaryContainedTarget (X i) (X (i+1))) (ordinaryContainedTarget (X i) (T (i+1)))
        (ordinaryContainedTarget (Z i) (Z (i+1))) (ordinaryContainedTarget (Z i) (W (i+1))) r
        (cost (i+1)) (deepCost (i+1)))→
    HasOrdinaryWheelDecomposition Q H r:=by
  intro Q₀ H₀ hfirst hXX hTX hZZ hWZ hc0 hd0 hlocal
  apply ordinary_protected_trace_coverdown_level_chain Q P F H Hbase r m Wterm Bterm hsize hbal hdiv hQP hHbase
    A hA hdecA hres L hL X T Z W cost deepCost hW hB
  intro i hi S G Hs ht heq hG hH hb hd
  exact ordinary_protected_trace_coverdown_cases Q₀ F H₀ r L X T Z W cost deepCost
    hfirst hXX hTX hZZ hWZ hc0 hd0 hlocal i hi S G Hs ht heq hb hd
end Oberwolfach
