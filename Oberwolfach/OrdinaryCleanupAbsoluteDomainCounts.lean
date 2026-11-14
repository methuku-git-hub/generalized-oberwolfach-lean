module

public import Oberwolfach.OrdinaryCleanupParentProfiles
public import Oberwolfach.OrdinaryRestrictedChanges
public import Oberwolfach.FixedHubDomainCounts

@[expose] public section
/-! The two-sided local row and hub profiles survive the actual symmetric
    edits, uniformly for every permitted set of roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_cleanup_absolute_domain_counts
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (pR pH density tR tH L βe βh:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A B pR pH density tR tH L βe βh s j σ):
    (∀S:Finset V,∀J:Finset U,S.card≤2→J.card≤2→
      |((common (common A S (fun v=>Q.neighborFinset v)) J
          (fun u=>Finset.univ.filter (fun v=>H v u))).card:ℝ)-
        pR^S.card*pH^J.card*(common A S (fun v=>P.neighborFinset v)).card|≤
          tR+S.card*L+J.card*L) ∧
    (∀S:Finset V,S.card≤3→(∀v∈S,∀w∈S,¬F.Adj v w)→
      |((common B S (fun v=>Finset.univ.filter (H v))).card:ℝ)-pH^S.card*B.card|≤tH+S.card*L):=by
  have hQ:∀v,((changed (A∩(rawWheelGraph P σ).neighborFinset v) (A∩Q.neighborFinset v)).card:ℝ)≤L:=by
    intro v
    exact (Nat.cast_le.mpr (changed_inter_card_le A _ _)).trans (profile.rim_edit v)
  have hrow:∀v,((changed (B∩Finset.univ.filter (rawWheelSpokes π d σ j v))
      (B∩Finset.univ.filter (H v))).card:ℝ)≤L:=by
    intro v
    exact (Nat.cast_le.mpr (changed_inter_card_le B _ _)).trans (profile.spoke_row_edit v)
  have hcol:∀u,((changed (A∩Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v u))
      (A∩Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L:=by
    intro u
    exact (Nat.cast_le.mpr (changed_inter_card_le A _ _)).trans (profile.spoke_column_edit u)
  constructor
  · intro S J hS hJ
    have hb:|((common (common A S (fun v=>(rawWheelGraph P σ).neighborFinset v)) J
          (fun u=>Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v u))).card:ℝ)-
        pR^S.card*pH^J.card*(common A S (fun v=>P.neighborFinset v)).card|≤tR:=by
      simpa only [profile.spoke_probability,Finset.prod_const] using (profile.rows S J hS hJ).le
    exact fixed_domain_mixed_target_stability A S J
      (fun v=>(rawWheelGraph P σ).neighborFinset v) (fun v=>Q.neighborFinset v)
      (fun u=>Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v u))
      (fun u=>Finset.univ.filter (fun v=>H v u)) L L _ tR
      (fun v _=>hQ v) (fun u _=>hcol u) hb
  · intro S hS hfree
    have hb:|((common B S (fun v=>Finset.univ.filter (rawWheelSpokes π d σ j v))).card:ℝ)-pH^S.card*B.card|≤tH:=
      (profile.columns S hS hfree).le
    exact target_stability (fixed_domain_neighbourhood_stability B S
      (fun v=>Finset.univ.filter (rawWheelSpokes π d σ j v))
      (fun v=>Finset.univ.filter (H v)) L (fun v _=>hrow v)) hb
end Oberwolfach
