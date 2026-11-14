module

public import Oberwolfach.OrdinaryCleanupParentProfiles
public import Oberwolfach.OrdinaryRestrictedChanges

@[expose] public section
/-! The same fixed-domain sample controls actual spoke columns after the
    cleanup edit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_cleanup_spoke_column_degrees
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ) (I:Finset V) (B:Finset U)
    (pR pH density tR tH L βe βh:ℝ) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d I B pR pH density tR tH L βe βh s j raw):
    ∀u,|((I.filter (fun v=>H v u)).card:ℝ)-pH*I.card|≤tR+L:=by
  let Hraw:=rawWheelSpokes π d raw j
  have hst:=ordinary_restricted_row_column_changes Hraw H I B L profile.spoke_row_edit profile.spoke_column_edit
  intro u
  have hh:=profile.rows ∅ {u} (by simp) (by simp)
  have he:common (common I (∅:Finset V) (fun x=>(rawWheelGraph P raw).neighborFinset x))
      ({u}:Finset U) (fun a=>Finset.univ.filter (fun z=>Hraw z a))=I.filter (fun v=>Hraw v u):=by
    ext v;simp [mem_common_iff]
  have hbase:common I (∅:Finset V) (fun x=>P.neighborFinset x)=I:=by ext v;simp [mem_common_iff]
  rw [he,hbase] at hh
  simp only [Finset.card_empty,pow_zero,Finset.prod_singleton,one_mul,profile.spoke_probability u] at hh
  have hchange:((changed (I.filter (fun v=>Hraw v u)) (I.filter (fun v=>H v u))).card:ℝ)≤L:=hst.2 u
  have hdiff:=card_difference_le_changed (I.filter (fun v=>Hraw v u)) (I.filter (fun v=>H v u))
  have habs:|((I.filter (fun v=>Hraw v u)).card:ℝ)-((I.filter (fun v=>H v u)).card:ℝ)|≤L:=hdiff.trans hchange
  have h1:=abs_lt.mp hh
  have h2:=abs_le.mp habs
  apply abs_le.mpr
  constructor <;> linarith
end Oberwolfach
