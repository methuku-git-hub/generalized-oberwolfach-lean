module

public import Oberwolfach.MarkedRetainedRobustChangeEvent

@[expose] public section
/-! Convert the common event's retained-spoke agreement sums to the exact
row and column card bounds needed by the corrected residual. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_retained_agreement_card_bounds
    (π:Equiv.Perm V) (d:ℕ) (σ raw:RawMarkedOutcome V U Γ Color)
    (g:Γ) (j:Color) (H:Bool→V→U→Prop) (row col:ℝ)
    (hinterval:∀e,σ (Sum.inr e)=raw (Sum.inr e))
    (hrow:∀v,(∑u,if ¬(rawMarkedPairSpokes π d σ g j false v u↔H false v u) then (1:ℝ) else 0)≤row)
    (hcol:∀u,(∑v,if ¬(rawMarkedPairSpokes π d σ g j false v u↔H false v u) then (1:ℝ) else 0)≤col):
    (∀v,((Finset.univ.filter (fun u=>¬(H false v u↔rawMarkedPairSpokes π d raw g j false v u))).card:ℝ)≤row) ∧
    (∀u,((Finset.univ.filter (fun v=>¬(H false v u↔rawMarkedPairSpokes π d raw g j false v u))).card:ℝ)≤col):=by
  have heq:(fun e=>σ (Sum.inr e))=(fun e=>raw (Sum.inr e)):=funext hinterval
  have hs:rawMarkedPairSpokes π d σ g j=rawMarkedPairSpokes π d raw g j:=by
    unfold rawMarkedPairSpokes
    rw [heq]
  constructor
  · intro v
    apply le_trans ?_ (hrow v)
    simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    apply Finset.sum_le_sum
    intro u _
    rw [hs]
    split_ifs <;> first | rfl | (exfalso;tauto)
  · intro u
    apply le_trans ?_ (hcol u)
    simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
    apply Finset.sum_le_sum
    intro v _
    rw [hs]
    split_ifs <;> first | rfl | (exfalso;tauto)
end Oberwolfach
