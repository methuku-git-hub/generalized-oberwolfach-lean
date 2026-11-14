module

public import Oberwolfach.TriangleHubTradeDisjointness

@[expose] public section
/-! Choose the physical rim graphs for all hub switches at once. Their
rim and spoke resources remain disjoint across the separate switches. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U J:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def TriangleHubTradeAt (G:SimpleGraph V) (H:V→U→Prop) (A Z:Finset V) (u u':U) (R:SimpleGraph V):Prop:=
    let Splus:V→U→Prop:=fun v z=>(v∈A∪Z∧z=u)∨(v∈A∧z=u')
    let Sminus:V→U→Prop:=fun v z=>(v∈A∪Z∧z=u')∨(v∈A∧z=u)
    HasOrdinaryWheelDecomposition R Splus 3 ∧ HasOrdinaryWheelDecomposition R Sminus 3 ∧
    HasResourceDecomposition (ordinaryWheelResources (P:=G) (F:=⊥) (Hbase:=H) (r:=3)) (ordinaryHostResources R Splus) ∧
    HasResourceDecomposition (ordinaryWheelResources (P:=G) (F:=⊥) (Hbase:=H) (r:=3)) (ordinaryHostResources R Sminus) ∧
    R≤G ∧ (∀ v w,R.Adj v w→v∈A∪Z ∧ w∈A∪Z) ∧ (∀ v w,v∈Z→w∈Z→¬R.Adj v w) ∧
    (∀ v z,Splus v z→H v z) ∧ (∀ v z,Sminus v z→H v z) ∧
    (∀ e:Sym2 V⊕(V×U),
      (if e∈ordinaryHostResources R Splus then (1:ℤ) else 0)-
      (if e∈ordinaryHostResources R Sminus then 1 else 0)=
      (if e∈Z.image (fun v=>Sum.inr (v,u)) then 1 else 0)-
      (if e∈Z.image (fun v=>Sum.inr (v,u')) then 1 else 0))

theorem triangle_hub_trades_choose_simultaneously (G:SimpleGraph V) (H:V→U→Prop)
    (A Z:J→Finset V) (u u':J→U)
    (hpair:∀ i j,i≠j→Disjoint (A i∪Z i) (A j∪Z j))
    (htrade:∀ i,TriangleHubTradeConclusion G H (A i) (Z i) (u i) (u' i)):
    ∃ R:J→SimpleGraph V,
      (∀ i,TriangleHubTradeAt G H (A i) (Z i) (u i) (u' i) (R i)) ∧
      (∀ i j,i≠j→Disjoint (R i) (R j)) ∧
      let Sp:J→V→U→Prop:=fun i v z=>(v∈A i∪Z i∧z=u i)∨(v∈A i∧z=u' i)
      let Sm:J→V→U→Prop:=fun i v z=>(v∈A i∪Z i∧z=u' i)∨(v∈A i∧z=u i)
      ∀ i j,i≠j→∀ v z,¬(Sp i v z∧Sp j v z) ∧ ¬(Sm i v z∧Sm j v z):=by
  have hex:∀ i,∃ R,TriangleHubTradeAt G H (A i) (Z i) (u i) (u' i) R:=by
    intro i
    exact htrade i
  choose R hR using hex
  refine ⟨R,hR,?_,?_⟩
  · apply triangle_hub_trade_rims_disjoint A Z R
    · intro i v w h
      exact (hR i).2.2.2.2.2.1 v w h
    · exact hpair
  · exact triangle_hub_trade_spokes_disjoint A Z u u' hpair
end Oberwolfach
