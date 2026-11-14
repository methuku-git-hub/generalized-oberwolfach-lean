module

public import Oberwolfach.OrdinaryDeepRowCountsStability
public import Oberwolfach.OrdinaryDeepIndexCountsStability
public import Oberwolfach.OrdinaryCleanupParentProfiles
public import Oberwolfach.OrdinaryRestrictedChanges

@[expose] public section
/-! The deeper original sample and the actual cleanup edit profile supply
the typed endpoint common-neighborhood estimates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_deep_counts_from_cleanup
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (pR pH density tR tH L βe βh ε:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A B pR pH density tR tH L βe βh s j σ)
    (deep:RawOrdinaryRows P π d 3 A pR s j tR σ)
    (hL:0≤L) (hrowbudget:tR+4*L≤ε*A.card) (hindexbudget:tH+3*L≤ε*B.card):
    EndpointTypedDeepCounts P Q F H A B pR pH ε:=by
  have hQ:∀v,((changed (A∩(rawWheelGraph P σ).neighborFinset v) (A∩Q.neighborFinset v)).card:ℝ)≤L:=by
    intro v
    exact (Nat.cast_le.mpr (changed_inter_card_le A _ _)).trans (profile.rim_edit v)
  have hrow:∀v,((changed (B∩Finset.univ.filter (rawWheelSpokes π d σ j v))
      (B∩Finset.univ.filter (H v))).card:ℝ)≤L:=by
    intro v
    exact (Nat.cast_le.mpr (changed_inter_card_le B _ _)).trans (profile.spoke_row_edit v)
  have hcol:∀u∈B,((changed (A∩Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v u))
      (A∩Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L:=by
    intro u hu
    exact (Nat.cast_le.mpr (changed_inter_card_le A _ _)).trans (profile.spoke_column_edit u)
  have hr:∀S:Finset V,∀J:Finset U,J⊆B→S.card≤3→J.card≤2→S.card+J.card≤4→
      |((common (common A S (fun v=>(rawWheelGraph P σ).neighborFinset v)) J
        (fun u=>Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v u))).card:ℝ)-
        pR^S.card*pH^J.card*(common A S (fun v=>P.neighborFinset v)).card|≤tR:=by
    intro S J hJ hS hJc hSJ
    simpa only [profile.spoke_probability,Finset.prod_const] using (deep S J hS (by omega)).le
  have hi:∀S:Finset V,S.card≤3→(∀v∈S,∀w∈S,¬F.Adj v w)→
      |((common B S (fun v=>Finset.univ.filter (rawWheelSpokes π d σ j v))).card:ℝ)-pH^S.card*B.card|≤tH:=by
    intro S hS hfree
    exact (profile.columns S hS hfree).le
  constructor
  · exact ordinary_deep_row_counts_stability P (rawWheelGraph P σ) Q F (rawWheelSpokes π d σ j) H A B
      pR pH tR L ε profile.rim_nonneg profile.spoke_nonneg hL hrowbudget hQ hcol hr
  · exact ordinary_deep_index_counts_stability F (rawWheelSpokes π d σ j) H B pH tH L ε hL hindexbudget hrow hi
end Oberwolfach
