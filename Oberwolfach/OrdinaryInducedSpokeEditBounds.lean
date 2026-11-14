module

public import Oberwolfach.OrdinaryLocalInducedEquiv
public import Oberwolfach.OrdinaryBoundaryRootSets
public import Oberwolfach.Neighbourhoods

@[expose] public section
/-! Restricting a spoke-column edit to an inner vertex set cannot increase
its symmetric-difference size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_induced_spoke_change_le_ambient
    (H H' : V → U → Prop) (A : Finset V) (Z : Finset U) (u : {u : U // u ∉ Z}) :
    ((changed
      (Finset.univ.filter (fun x : {x : V // x ∈ A} => H x.val u.val))
      (ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H' Z A u))).card : ℝ) ≤
    ((changed (Finset.univ.filter (fun x => H x u.val))
      (Finset.univ.filter (fun x => H' x u.val))).card : ℝ) := by
  have hi : (changed
      (Finset.univ.filter (fun x : {x : V // x ∈ A} => H x.val u.val))
      (ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H' Z A u))).card ≤
      (changed (Finset.univ.filter (fun x => H x u.val))
        (Finset.univ.filter (fun x => H' x u.val))).card := by
    apply Finset.card_le_card_of_injOn Subtype.val
    · intro x hx
      change x ∈ changed
        (Finset.univ.filter (fun x : {x : V // x ∈ A} => H x.val u.val))
        (ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H' Z A u)) at hx
      change x.val ∈ changed (Finset.univ.filter (fun x => H x u.val))
        (Finset.univ.filter (fun x => H' x u.val))
      simpa only [changed, Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter,
        Finset.mem_univ, true_and, ordinaryInducedLocalDomain, ordinaryBoundaryHubSet,
        x.property, and_true, true_and] using hx
    · intro a _ b _ h
      exact Subtype.val_injective h
  exact_mod_cast hi
end Oberwolfach
