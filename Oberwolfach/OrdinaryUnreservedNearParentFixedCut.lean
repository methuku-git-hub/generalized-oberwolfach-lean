module

public import Oberwolfach.OrdinaryUnreservedPackingNearParent
public import Oberwolfach.OrdinaryNearBalanceCutWeaken

@[expose] public section
/-! Fix the packing cut constant before choosing the later reserve scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 2048
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_unreserved_near_parent_packing_data_fixed_cut
    (r:ℕ) (hr:3≤r) (k:ℕ) (α ω β₀ β bminus bplus h hpack δ ε₀ εstar η ξ ζ p ε f b c:ℝ)
    (P Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U) (σ:Sym2 (V⊕U)→Bool)
    (hcut:hpack≤h-ξ-ζ)
    (d:OrdinaryUnreservedNearParentData r hr k α ω β₀ β bminus bplus h δ ε₀ εstar η ξ ζ p ε f b c P Q F H X Z σ):
    let R:=retainedGraph (ordinaryBoundaryGraph Q H X Z) σ;
    Nonempty (OrdinaryNearBalancePackingData r hr k α ω β bminus bplus hpack δ εstar η P
      (ordinaryUnreservedRim Q X R) F (ordinaryUnreservedSpokes H X Z R)):=by
  intro R
  obtain ⟨D⟩:=ordinary_unreserved_packing_data_from_near_parent r hr k α ω β₀ β bminus bplus h δ
    ε₀ εstar η ξ ζ p ε f b c P Q F H X Z σ d
  exact ordinary_near_balance_data_weaken_cut r hr k α ω β bminus bplus (h-ξ-ζ) hpack δ εstar η
    P (ordinaryUnreservedRim Q X R) F (ordinaryUnreservedSpokes H X Z R) hcut D
end Oberwolfach
