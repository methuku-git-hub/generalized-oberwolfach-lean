module

public import Oberwolfach.OrdinaryUnreservedOrientation
public import Oberwolfach.OrdinaryReserveCutStability

@[expose] public section
/-! The original rim and spoke large-cut bounds survive deleting the inner
rectangle and the bounded-degree physical reserve. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_unreserved_cuts
    (Q:SimpleGraph V) (H:V→U→Prop) (A:V→V→ℕ) (X:Finset V) (Z:Finset U)
    (R:SimpleGraph (V⊕U)) (δ h ξ ζ:ℝ)
    (hn:0<Fintype.card V) (hm:0<Fintype.card U) (hξ:0≤ξ) (hζ:0≤ζ)
    (hA:∀x y,A x y+A y x=if Q.Adj x y then 1 else 0)
    (hX:(X.card:ℝ)≤ξ*Fintype.card V) (hZ:(Z.card:ℝ)≤ξ*Fintype.card U)
    (hRrim:∀v,(R.degree (Sum.inl v):ℝ)≤ζ*Fintype.card V)
    (hRrow:∀v,(R.degree (Sum.inl v):ℝ)≤ζ*Fintype.card U)
    (hRcol:∀u,(R.degree (Sum.inr u):ℝ)≤ζ*Fintype.card V)
    (hcutA:BipartiteLargeCut A δ h) (hcutH:BipartiteLargeCut (relationMultiplicity H) δ h):
    (∀x y,ordinaryUnreservedOrientation A X R x y+ordinaryUnreservedOrientation A X R y x=
      if (ordinaryUnreservedRim Q X R).Adj x y then 1 else 0) ∧
    BipartiteLargeCut (ordinaryUnreservedOrientation A X R) δ (h-ξ-ζ) ∧
    BipartiteLargeCut (relationMultiplicity (ordinaryUnreservedSpokes H X Z R)) δ (h-ξ-ζ):=by
  have hArel:BipartiteLargeCut (relationMultiplicity (fun v w=>A v w=1)) δ h:=by
    rw [←ordinary_orientation_is_indicator Q A hA]
    exact hcutA
  have hrectA:=bipartiteLargeCut_delete_rectangle hn hn (fun v w=>A v w=1) X X δ h ξ hξ hX hX hArel
  have hrectH:=bipartiteLargeCut_delete_rectangle hn hm H X Z δ h ξ hξ hX hZ hcutH
  have hr:=ordinary_reserve_rim_cut_stability (fun v w=>A v w=1∧¬(v∈X∧w∈X)) R δ (h-ξ) ζ hn hζ hRrim hrectA
  have hs:=ordinary_reserve_spoke_cut_stability (fun v u=>H v u∧¬(v∈X∧u∈Z)) R δ (h-ξ) ζ hn hm hζ hRrow hRcol hrectH
  refine ⟨ordinary_unreserved_orientation_graph Q A X R hA,?_,?_⟩
  · rw [ordinary_unreserved_orientation_indicator Q A X R hA]
    simpa only [and_assoc] using hr
  · change BipartiteLargeCut (relationMultiplicity
      (fun v u=>H v u∧¬(v∈X∧u∈Z)∧¬R.Adj (Sum.inl v) (Sum.inr u))) δ (h-ξ-ζ)
    simpa only [and_assoc] using hs
end Oberwolfach
