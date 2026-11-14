module

public import Oberwolfach.OrdinaryPreCoverPackingInputs
public import Oberwolfach.OrdinaryNearBalanceCutWeaken

@[expose] public section
/-! Compact assumptions for the pre-cover to post-cover packing bridge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_precover_packing_data_fixed_cut
    (r:ℕ) (hr:3≤r) (k:ℕ) (α ω βparent β b B h hpack δ εparent εstar η ξ ζ p ε f binner c L:ℝ)
    (P Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (C:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool)
    (hcut:hpack≤h-ξ-ζ)
    (d:OrdinaryPreCoverPackingInputs r hr k α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c L
      P Q F H X Z C σ):
    let Q':=Q\C.comap Sum.inl;let H':=fun v u=>H v u∧¬C.Adj (Sum.inl v) (Sum.inr u);
    let R:=retainedGraph (ordinaryBoundaryGraph Q' H' X Z) σ;
    Nonempty (OrdinaryNearBalancePackingData r hr k α ω β b B hpack δ εstar η P
      (ordinaryUnreservedRim Q' X R) F (ordinaryUnreservedSpokes H' X Z R)):=by
  intro Q' H' R
  obtain ⟨d'⟩:=ordinary_precover_packing_data_of_inputs r hr k α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c L
    P Q F H X Z C σ d
  exact ordinary_near_balance_data_weaken_cut r hr k α ω β b B (h-ξ-ζ) hpack δ εstar η P
    (ordinaryUnreservedRim Q' X R) F (ordinaryUnreservedSpokes H' X Z R) hcut d'
end Oberwolfach
