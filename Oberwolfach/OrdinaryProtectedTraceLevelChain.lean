module

public import Oberwolfach.OrdinaryProtectedTraceInvariant
public import Oberwolfach.OrdinaryTerminalRemainderBalance

@[expose] public section
/-! The protected chain's initial, advance, and terminal conditions follow
from an explicit deletion history. The analytic cover-down input and terminal
absorber remain hypotheses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_protected_trace_coverdown_level_chain
    (Q P F:SimpleGraph V) (H Hbase:V→U→Prop) (r m:ℕ)
    (W:Finset V) (B:Finset U) (hsize:W.card+B.card≤m)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (hQP:Q≤P) (hHbase:∀v u,H v u→Hbase v u)
    (A:Finset (Sym2 V⊕(V×U))) (hA:A⊆ordinaryHostResources Q H)
    (hdecA:HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r)) A)
    (hres:∀(G':SimpleGraph V) (H':V→U→Prop),
      ordinaryHostResources G' H'⊆ordinaryRootResources W B →
      (ordinaryPhysicalGraph G' H').support.toFinset.card≤m →
      (∀v,G'.degree v=2*(Finset.univ.filter (H' v)).card) →
      (∀u,r∣(Finset.univ.filter (fun v=>H' v u)).card) →
      G'≤P → (∀v u,H' v u→Hbase v u) →
      IsResourceAbsorber (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r))
        (ordinaryHostResources G' H') A)
    (L:ℕ) (hL:0<L) (X Tdeep:ℕ→Finset V) (Z Wdeep:ℕ→Finset U) (cost deepCost:ℕ→ℝ)
    (hW:X (L-1)=W) (hB:Z (L-1)=B):
    let Q₀:=Q\ordinaryResourceRim Q A;
    let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈A);
    (∀i<L,∀S (G:SimpleGraph V) (Hs:V→U→Prop),
      OrdinaryProtectedTrace Q₀ H₀ X Tdeep Z Wdeep cost deepCost i S→
      ordinaryHostResources G Hs=S→G≤Q→(∀v u,Hs v u→H v u)→
      (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
      (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card)→
      OrdinaryProtectedHostCoverDownResult G F Hs (X i) (Tdeep i) (Z i) (Wdeep i) r (cost i) (deepCost i))→
    HasOrdinaryWheelDecomposition Q H r:=by
  intro Q₀ H₀ hCover
  have hbase:ordinaryHostResources Q₀ H₀=ordinaryHostResources Q H\A:=by
    obtain ⟨_,_,hreal⟩:=ordinary_resource_subgraph Q H A hA
    rw [show ordinaryHostResources Q₀ H₀=ordinaryHostResources
      (Q\ordinaryResourceRim Q A) (fun v u=>H v u∧¬(Sum.inr (v,u)∈A)) from rfl]
    rw [ordinaryHostResources_sdiff,hreal]
  apply ordinary_protected_coverdown_level_chain Q P F H Hbase r m W B hsize hbal hdiv hQP hHbase A hA hdecA hres
    L X Tdeep Z Wdeep cost deepCost (OrdinaryProtectedTrace Q₀ H₀ X Tdeep Z Wdeep cost deepCost)
  · rw [←hbase]
    exact ordinary_protected_trace_initial Q₀ H₀ X Tdeep Z Wdeep cost deepCost
  · exact hCover
  · intro i hi S G Hs htrace hstate D E hDG hEH Gnext Hnext hroot hnb hnd hcost hdeepcost hdeep
    exact ordinary_protected_trace_advance Q₀ H₀ X Tdeep Z Wdeep cost deepCost i S G D Hs E
      htrace hstate hroot hcost hdeepcost hdeep
  · intro S htrace
    have ht:=ordinary_protected_trace_terminal Q₀ H₀ X Tdeep Z Wdeep cost deepCost L hL S htrace
    simpa only [hW,hB] using ht
end Oberwolfach
