module

public import Oberwolfach.OrdinaryUniformProtectedBalanceHistory
public import Oberwolfach.OrdinaryProtectedCoverDownLevelChainWithProperty

@[expose] public section
/-! A level chain preserves one wheel-deletion history with uniform
future-target discrepancy certificates, conditional on producing each step. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_uniform_protected_balance_level_chain
    (Q P F:SimpleGraph V) (H Hbase:V→U→Prop) (r m:ℕ)
    (Wterm:Finset V) (Bterm:Finset U) (hsize:Wterm.card+Bterm.card≤m)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (hQP:Q≤P) (hHbase:∀v u,H v u→Hbase v u)
    (A:Finset (Sym2 V⊕(V×U))) (hA:A⊆ordinaryHostResources Q H)
    (hdecA:HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r)) A)
    (hres:∀(G':SimpleGraph V) (H':V→U→Prop),
      ordinaryHostResources G' H'⊆ordinaryRootResources Wterm Bterm→
      (ordinaryPhysicalGraph G' H').support.toFinset.card≤m→
      (∀v,G'.degree v=2*(Finset.univ.filter (H' v)).card)→
      (∀u,r∣(Finset.univ.filter (fun v=>H' v u)).card)→
      G'≤P→(∀v u,H' v u→Hbase v u)→
      IsResourceAbsorber (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=Hbase) (r:=r))
        (ordinaryHostResources G' H') A)
    (L:ℕ) (hL:0<L) (X T:ℕ→Finset V) (Z W:ℕ→Finset U) (cost deepCost:ℕ→ℝ)
    (I Parent:ℕ→Finset V) (J:ℕ→Finset U) (window:ℕ→Finset ℕ) (inner cross:ℕ→ℕ→ℝ)
    (hW:X (L-1)=Wterm) (hB:Z (L-1)=Bterm):
    let Q₀:=Q\ordinaryResourceRim Q A;
    let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈A);
    let GoodDel:=fun i (D:SimpleGraph V) (E:V→U→Prop)=>
      (∀target<L,i∈window target→∀v∈I target,
        ordinaryWheelInnerBoundaryError D E (I target) (J target) v≤ inner target i) ∧
      (∀target<L,i∈window target→∀v∈Parent target,v∉I target→
        ordinaryWheelCrossError D E (I target) (J target) v≤ cross target i);
    (∀i<L,∀S (G:SimpleGraph V) (Hs:V→U→Prop),
      OrdinaryUniformProtectedBalanceHistory Q₀ H₀ X T Z W cost deepCost r i L S I Parent J window inner cross→
      ordinaryHostResources G Hs=S→G≤Q→(∀v u,Hs v u→H v u)→
      (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
      (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card)→
      OrdinaryProtectedHostCoverDownWithProperty G F Hs (X i) (T i) (Z i) (W i) r (cost i) (deepCost i) (GoodDel i))→
    HasOrdinaryWheelDecomposition Q H r :=by
  intro Q₀ H₀ GoodDel hCover
  have hbase:ordinaryHostResources Q₀ H₀=ordinaryHostResources Q H\A:=by
    obtain ⟨_,_,hreal⟩:=ordinary_resource_subgraph Q H A hA
    rw [show ordinaryHostResources Q₀ H₀=ordinaryHostResources
      (Q\ordinaryResourceRim Q A) (fun v u=>H v u∧¬(Sum.inr (v,u)∈A)) from rfl]
    rw [ordinaryHostResources_sdiff,hreal]
  let Good:=fun i S=>Nonempty (OrdinaryUniformProtectedBalanceHistory Q₀ H₀ X T Z W cost deepCost r i L S I Parent J window inner cross)
  apply ordinary_protected_coverdown_level_chain_with_property Q P F H Hbase r m Wterm Bterm hsize hbal hdiv hQP hHbase A hA hdecA hres
    L X T Z W cost deepCost Good GoodDel
  · rw [←hbase]
    exact ⟨ordinary_uniform_protected_balance_history_initial Q₀ H₀ X T Z W cost deepCost r L I Parent J window inner cross⟩
  · intro i hi S G Hs hgood hstate hG hHs hb hd
    obtain ⟨hist⟩:=hgood
    exact hCover i hi S G Hs hist hstate hG hHs hb hd
  · intro i hi S G Hs hgood hstate D E hDG hEH hdec hprop Gnext Hnext hroot hnb hnd hcost hdeepcost hdeep
    obtain ⟨hist⟩:=hgood
    exact ⟨ordinary_uniform_protected_balance_history_advance Q₀ H₀ X T Z W cost deepCost r i L S
      I Parent J window inner cross hist G D Hs E hstate hDG hEH hdec hroot hcost hdeepcost hdeep hprop.1 hprop.2⟩
  · intro S hgood
    obtain ⟨hist⟩:=hgood
    rcases hist.trace.2.1 with hz | hroot
    · omega
    · simpa only [hW,hB] using hroot
end Oberwolfach
