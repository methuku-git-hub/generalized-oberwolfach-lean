module

public import Oberwolfach.OrdinaryUnreservedCuts
public import Oberwolfach.OrdinaryBoundaryReserveJointEvent

@[expose] public section
/-! Reserve concentration supplies the physical degree hypotheses used to
preserve the actual unreserved rim and spoke cuts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_boundary_reserve_total_degree (Q:SimpleGraph V) (H:V→U→Prop)
    (X:Finset V) (Z:Finset U) (p ε:ℝ) (hp:0≤p) (σ:Sym2 (V⊕U)→Bool)
    (hgood:OrdinaryBoundaryReserveGood Q H X Z p ε σ):
    ∀w,((retainedGraph (ordinaryBoundaryGraph Q H X Z) σ).degree w:ℝ)≤(p+ε)*Fintype.card (V⊕U):=by
  intro w
  let G:=ordinaryBoundaryGraph Q H X Z
  have hn:(G.degree w:ℝ)≤Fintype.card (V⊕U):=by
    rw [←SimpleGraph.card_neighborFinset_eq_degree]
    exact_mod_cast (Finset.card_le_univ (G.neighborFinset w))
  have ht:=(abs_lt.mp (hgood.1 w)).2
  have hh:=mul_le_mul_of_nonneg_left hn hp
  nlinarith only [ht,hh]

theorem ordinary_unreserved_cuts_from_reserve
    (Q:SimpleGraph V) (H:V→U→Prop) (A:V→V→ℕ) (X:Finset V) (Z:Finset U)
    (σ:Sym2 (V⊕U)→Bool) (δ h ξ ζ p ε:ℝ)
    (hn:0<Fintype.card V) (hm:0<Fintype.card U) (hξ:0≤ξ) (hζ:0≤ζ) (hp:0≤p)
    (hgood:OrdinaryBoundaryReserveGood Q H X Z p ε σ)
    (hscaleV:(p+ε)*Fintype.card (V⊕U)≤ζ*Fintype.card V)
    (hscaleU:(p+ε)*Fintype.card (V⊕U)≤ζ*Fintype.card U)
    (hA:∀x y,A x y+A y x=if Q.Adj x y then 1 else 0)
    (hX:(X.card:ℝ)≤ξ*Fintype.card V) (hZ:(Z.card:ℝ)≤ξ*Fintype.card U)
    (hcutA:BipartiteLargeCut A δ h) (hcutH:BipartiteLargeCut (relationMultiplicity H) δ h):
    let R:=retainedGraph (ordinaryBoundaryGraph Q H X Z) σ;
    (∀x y,ordinaryUnreservedOrientation A X R x y+ordinaryUnreservedOrientation A X R y x=
      if (ordinaryUnreservedRim Q X R).Adj x y then 1 else 0) ∧
    BipartiteLargeCut (ordinaryUnreservedOrientation A X R) δ (h-ξ-ζ) ∧
    BipartiteLargeCut (relationMultiplicity (ordinaryUnreservedSpokes H X Z R)) δ (h-ξ-ζ):=by
  intro R
  have hdeg:=ordinary_boundary_reserve_total_degree Q H X Z p ε hp σ hgood
  exact ordinary_unreserved_cuts Q H A X Z R δ h ξ ζ hn hm hξ hζ hA hX hZ
    (fun v=>(hdeg (Sum.inl v)).trans hscaleV) (fun v=>(hdeg (Sum.inl v)).trans hscaleU)
    (fun u=>(hdeg (Sum.inr u)).trans hscaleV) hcutA hcutH
end Oberwolfach
