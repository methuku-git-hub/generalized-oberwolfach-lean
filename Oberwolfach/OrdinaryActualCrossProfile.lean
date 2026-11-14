module

public import Oberwolfach.OrdinarySampledCrossProfile
public import Oberwolfach.OrdinaryCrossBalanceFromChanges

@[expose] public section
/-! Transfer the original sample's two-domain profiles through bounded
symmetric rim and spoke edits. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_actual_cross_balance_from_sample
    (P F Q:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ) (I:Finset V) (J:Finset U)
    (pR pH tR tH e L:ℝ) (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (hrows:RawOrdinaryRows P π d 2 I pR s j tR σ)
    (hcols:RawOrdinaryDomainIndices F π d 3 J pH j tH σ)
    (hparent:∀v,|pR*(P.neighborFinset v∩I).card-2*pH*J.card|≤e)
    (hrim:∀v,((changed (Q.neighborFinset v) ((rawWheelGraph P σ).neighborFinset v)).card:ℝ)≤L)
    (hspoke:∀v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (rawWheelSpokes π d σ j v))).card:ℝ)≤L):
    ∀v,|((Q.neighborFinset v∩I).card:ℝ)-2*(J.filter (H v)).card|≤e+tR+2*tH+3*L:=by
  have hh:=ordinary_sampled_single_root_profiles P F π d I J pR pH tR tH s j σ hrows hcols
  intro v
  have hfilter (f:U→Prop):(Finset.univ.filter f)∩J=J.filter f:=by ext u;simp [and_comm]
  have hS:|(((Finset.univ.filter (rawWheelSpokes π d σ j v))∩J).card:ℝ)-pH*J.card|≤tH:=by
    rw [hfilter]
    exact (hh.2 v).le
  have h:=ordinary_cross_balance_from_changes (Q.neighborFinset v) ((rawWheelGraph P σ).neighborFinset v)
    (P.neighborFinset v) I (Finset.univ.filter (H v)) (Finset.univ.filter (rawWheelSpokes π d σ j v)) J
    pR pH tR tH e L (hh.1 v).le hS (hparent v) (hrim v) (hspoke v)
  rw [hfilter] at h
  exact h
end Oberwolfach
