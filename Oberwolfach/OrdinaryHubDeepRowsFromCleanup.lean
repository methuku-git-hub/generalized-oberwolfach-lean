module

public import Oberwolfach.OrdinaryDeepRowCountsStability
public import Oberwolfach.OrdinaryCleanupParentProfiles
public import Oberwolfach.OrdinaryRestrictedChanges

@[expose] public section
/-! The deeper row event controls every hub root, including hubs outside the
protected inner hub set, after the same cleanup edits. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_hub_deep_rows_from_cleanup
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (pR pH density tR tH L βe βh ε:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A B pR pH density tR tH L βe βh s j σ)
    (deep:RawOrdinaryRows P π d 3 A pR s j tR σ)
    (hL:0≤L) (hbudget:tR+4*L≤ε*A.card):
    ∀u:U,∀S:Finset V,S.card≤3→
      pR^S.card*pH*(common A S (fun v=>(P\F).neighborFinset v)).card-ε*A.card≤
        ((common (A.filter (fun v=>H v u)) S (fun v=>Q.neighborFinset v)).card:ℝ):=by
  have hQ:∀v,((changed (A∩(rawWheelGraph P σ).neighborFinset v) (A∩Q.neighborFinset v)).card:ℝ)≤L:=by
    intro v
    exact (Nat.cast_le.mpr (changed_inter_card_le A _ _)).trans (profile.rim_edit v)
  have hJ:∀u∈(Finset.univ:Finset U),((changed (A∩Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v u))
      (A∩Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L:=by
    intro u hu
    exact (Nat.cast_le.mpr (changed_inter_card_le A _ _)).trans (profile.spoke_column_edit u)
  have hbase:∀S:Finset V,∀T:Finset U,T⊆Finset.univ→S.card≤3→T.card≤2→S.card+T.card≤4→
      |((common (common A S (fun v=>(rawWheelGraph P σ).neighborFinset v)) T
        (fun u=>Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v u))).card:ℝ)-
        pR^S.card*pH^T.card*(common A S (fun v=>P.neighborFinset v)).card|≤tR:=by
    intro S T hT hS hTc hST
    simpa only [profile.spoke_probability,Finset.prod_const] using (deep S T hS (by omega)).le
  have hh:=ordinary_deep_row_counts_stability P (rawWheelGraph P σ) Q F (rawWheelSpokes π d σ j) H A Finset.univ
    pR pH tR L ε profile.rim_nonneg profile.spoke_nonneg hL hbudget hQ hJ hbase
  intro u S hS
  have h:=hh S {u} (by simp) hS (by simp) (by simp;omega)
  have he:common (common A S (fun v=>Q.neighborFinset v)) {u}
      (fun u=>Finset.univ.filter (fun v=>H v u))=
      common (A.filter (fun v=>H v u)) S (fun v=>Q.neighborFinset v):=by
    ext v
    simp [common,and_comm,and_left_comm,and_assoc]
  simpa only [Finset.card_singleton,pow_one,he] using h
end Oberwolfach
