module

public import Oberwolfach.OrdinaryCleanupEndpointMixedProfiles
public import Oberwolfach.OrdinarySampledCrossProfile
public import Oberwolfach.OrdinaryEndpointRelativeCountArithmetic

@[expose] public section
/-! At each boundary endpoint the rim-spoke counts have the required
    relative target, after the same permitted edits. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_endpoint_rim_relative_profiles
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (pR pH density tR tH L βe βh:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A B pR pH density tR tH L βe βh s j σ):
    (∀x,|((A∩Q.neighborFinset x).card:ℝ)-pR*(A∩P.neighborFinset x).card|≤tR+L) ∧
    (∀x u,|((A.filter (fun v=>Q.Adj x v∧H v u)).card:ℝ)-pH*(A∩Q.neighborFinset x).card|≤
      (tR+2*L)+pH*(tR+L)):=by
  have hraw:=ordinary_sampled_single_root_profiles P F π d A B pR pH tR tH s j σ profile.rows profile.columns
  have hmix:=ordinary_cleanup_endpoint_mixed_profiles P Q F H A B π d j s pR pH density tR tH L βe βh σ profile
  have hsingle (x:V):|((A∩Q.neighborFinset x).card:ℝ)-pR*(A∩P.neighborFinset x).card|≤tR+L:=by
    have hc:((changed (A∩(rawWheelGraph P σ).neighborFinset x) (A∩Q.neighborFinset x)).card:ℝ)≤L:=
      (Nat.cast_le.mpr (changed_inter_card_le A _ _)).trans (profile.rim_edit x)
    have hd:=card_difference_le_changed (A∩(rawWheelGraph P σ).neighborFinset x) (A∩Q.neighborFinset x)
    have habs:|((A∩Q.neighborFinset x).card:ℝ)-(A∩(rawWheelGraph P σ).neighborFinset x).card|≤L:=by
      rw [abs_sub_comm]
      exact hd.trans hc
    have hbase:|((A∩(rawWheelGraph P σ).neighborFinset x).card:ℝ)-pR*(A∩P.neighborFinset x).card|≤tR:=by
      simpa only [Finset.inter_comm] using (hraw.1 x).le
    exact target_stability habs hbase
  refine ⟨hsingle,?_⟩
  intro x u
  have hh:=hmix x u
  have hY:|((A.filter (fun v=>Q.Adj x v∧H v u)).card:ℝ)-
      pH*(pR*(A∩P.neighborFinset x).card)|≤tR+2*L:=by
    convert hh using 1 <;> ring
  exact ordinary_relative_count_from_common_centre _ _ (pR*(A∩P.neighborFinset x).card) pH (tR+L) (tR+2*L)
    profile.spoke_nonneg (hsingle x) hY
end Oberwolfach
