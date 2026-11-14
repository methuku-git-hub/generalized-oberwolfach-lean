module

public import Oberwolfach.ResourceRootEmbedding
public import Oberwolfach.OrderedOrdinaryWheelExpectation
public import Oberwolfach.OrderedOrdinaryLocality

@[expose] public section
/-! Put ordinary candidates in the marked resource universe without
changing their roots, fixed weights, or realised sampling outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U C:Type} [Fintype V] [Fintype U] [Fintype C] [LinearOrder V] [DecidableEq U]

def ordinaryMarkedResourceEmbedding : (V×V)⊕(V×U) ↪ ((V×V)⊕(V×V))⊕(Bool×V×U) :=
  ⟨orderedOrdinaryResourceEmbedding,orderedOrdinaryResourceEmbedding_injective⟩

theorem ordinary_load_in_marked_universe
    (R:C→Finset ((V×V)⊕(V×U))) (w:C→ℝ)
    (rim:(V×V)⊕(V×V)→Prop) (spoke:Bool→V→U→Prop)
    (root:(V×V)⊕(V×U)):
    resourcePatternLoad (fun c=>(R c).map ordinaryMarkedResourceEmbedding) w
      (fun _ _=>true) (ordinaryMarkedResourceEmbedding root) (typedMarkedResourceState rim spoke) =
      resourcePatternLoad R w (fun _ _=>true) root
        (fun x=>typedMarkedResourceState rim spoke (orderedOrdinaryResourceEmbedding x)) := by
  exact resource_pattern_load_map R w ordinaryMarkedResourceEmbedding (typedMarkedResourceState rim spoke) root

theorem ordinary_load_zero_at_nonordinary_resource
    (R:C→Finset ((V×V)⊕(V×U))) (w:C→ℝ)
    (rim:(V×V)⊕(V×V)→Prop) (spoke:Bool→V→U→Prop)
    (root:((V×V)⊕(V×V))⊕(Bool×V×U))
    (hroot:∀x,orderedOrdinaryResourceEmbedding x≠root):
    resourcePatternLoad (fun c=>(R c).map ordinaryMarkedResourceEmbedding) w
      (fun _ _=>true) root (typedMarkedResourceState rim spoke)=0 := by
  exact resource_pattern_load_map_outside R w ordinaryMarkedResourceEmbedding _ root hroot

theorem ordinary_pair_weight_in_marked_universe
    (R:C→Finset ((V×V)⊕(V×U))) (w:C→ℝ)
    (u v:(V×V)⊕(V×U)):
    resourceOmittedPairWeight (fun c=>(R c).map ordinaryMarkedResourceEmbedding) w
      (ordinaryMarkedResourceEmbedding u) (ordinaryMarkedResourceEmbedding v)=
      resourceOmittedPairWeight R w u v := by
  exact resource_omitted_pair_weight_map R w ordinaryMarkedResourceEmbedding u v
/-- The ordinary concentration calculation is evaluated on exactly the
restriction of the marked construction's original outcome. -/
theorem ordinary_raw_load_in_marked_universe
    {Γ Color:Type} [Fintype Γ] [Fintype Color]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (g:Γ) (j:Color)
    (σ:RawMarkedOutcome V U Γ Color)
    (R:C→Finset ((V×V)⊕(V×U))) (w:C→ℝ) (root:(V×V)⊕(V×U)):
    resourcePatternLoad (fun c=>(R c).map ordinaryMarkedResourceEmbedding) w
      (fun _ _=>true) (ordinaryMarkedResourceEmbedding root)
      (typedMarkedResourceState (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j)) =
      resourcePatternLoad R w (fun _ _=>true) root
        (orderedOrdinaryResourceState P π d g j σ) := by
  exact ordinary_load_in_marked_universe R w (rawMarkedPairRims P π d σ)
    (rawMarkedPairSpokes π d σ g j) root
end Oberwolfach
