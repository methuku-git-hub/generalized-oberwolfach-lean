module

public import Oberwolfach.OrdinaryActualFiniteModels
public import Oberwolfach.OrdinaryComparisonIdentifiers
public import Oberwolfach.CanonicalGraphPairs

@[expose] public section

/-! Concrete finite order bounds for the expansion, attachment and
comparison graphs. These depend only on the original root order and r. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem simpleGraph_edges_le_square (G : SimpleGraph V) : G.edgeFinset.card≤(Fintype.card V)^2 := by
  rw [←canonicalGraphPairs_card G]
  have hh := Finset.card_le_univ (canonicalGraphPairs G)
  simpa only [Fintype.card_prod,pow_two] using hh

theorem actual_expansion_order_bound (G : SimpleGraph V) (H : V → U → Prop) (r m : ℕ)
    (hm : Fintype.card V+Fintype.card U≤m) :
    Fintype.card (ActualExpansionRow G H (Fin r))+Fintype.card (ActualExpansionHub G H)≤
      m+2*m^2*(r+1) := by
  have hV : Fintype.card V≤m := by omega
  have hU : Fintype.card U≤m := by omega
  have he : G.edgeFinset.card≤m^2 :=
    (simpleGraph_edges_le_square G).trans (Nat.pow_le_pow_left hV 2)
  have hs : Fintype.card (ActualSpoke H)≤m^2 := by
    have hh := Fintype.card_subtype_le (fun e:V×U=>H e.1 e.2)
    simp only [Fintype.card_prod] at hh
    exact hh.trans (by simpa only [pow_two] using Nat.mul_le_mul hV hU)
  have ho := ordinaryExpansion_order (V:=V) (U:=U) (E:=G.edgeFinset) (J:=ActualSpoke H) (W:=Fin r)
  simp only [Fintype.card_coe,Fintype.card_fin] at ho
  change Fintype.card (ExpansionRow V G.edgeFinset (ActualSpoke H) (Fin r))+
    Fintype.card (ExpansionHub U G.edgeFinset (ActualSpoke H))≤_
  rw [ho]
  have hsum : G.edgeFinset.card+Fintype.card (ActualSpoke H)≤2*m^2 := by omega
  exact Nat.add_le_add hm (Nat.mul_le_mul_right (r+1) hsum)

theorem ordinary_comparison_order_bound (G : SimpleGraph V) (r m : ℕ)
    (hV : Fintype.card V≤m) :
    Fintype.card (OrdinaryComparisonRows r (G.edgeFinset.card/r))+
      Fintype.card (OrdinaryComparisonHubs (G.edgeFinset.card/r))≤m^2*(r+2) := by
  have he : G.edgeFinset.card/r≤m^2 :=
    (Nat.div_le_self _ _).trans ((simpleGraph_edges_le_square G).trans (Nat.pow_le_pow_left hV 2))
  simp only [OrdinaryComparisonRows,OrdinaryComparisonHubs,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_empty,zero_add]
  nlinarith only [Nat.mul_le_mul_right (r+2) he]

end Oberwolfach
