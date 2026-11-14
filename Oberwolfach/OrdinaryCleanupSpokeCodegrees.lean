module

public import Oberwolfach.OrdinaryCleanupParentProfiles
public import Oberwolfach.OrdinaryBoundaryHubPairStability
public import Oberwolfach.OrdinaryRestrictedChanges

@[expose] public section
/-! A cleanup profile retains the sampled one- and two-row hub counts on
    the actual inner hub domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_cleanup_spoke_degrees_and_codegrees
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ) (I:Finset V) (B:Finset U)
    (pR pH density tR tH L βe βh:ℝ) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d I B pR pH density tR tH L βe βh s j raw):
    (∀v,|((B.filter (H v)).card:ℝ)-pH*B.card|≤tH+L) ∧
    (∀v w,v≠w→¬F.Adj v w→
      |((B.filter (fun u=>H v u∧H w u)).card:ℝ)-pH^2*B.card|≤tH+2*L):=by
  let Hraw:=rawWheelSpokes π d raw j
  have hst:=ordinary_restricted_row_column_changes Hraw H I B L profile.spoke_row_edit profile.spoke_column_edit
  constructor
  · intro v
    have hfree:∀a∈({v}:Finset V),∀b∈({v}:Finset V),¬F.Adj a b:=by
      intro a ha b hb
      simp only [Finset.mem_singleton] at ha hb
      subst a;subst b
      exact fun h=>F.irrefl h
    have hh:=profile.columns {v} (by simp) hfree
    have he:common B ({v}:Finset V) (fun x=>Finset.univ.filter (Hraw x))=B.filter (Hraw v):=by
      ext u;simp [mem_common_iff]
    rw [he] at hh
    simp only [Finset.card_singleton,pow_one] at hh
    have hchange:((changed (B.filter (Hraw v)) (B.filter (H v))).card:ℝ)≤L:=hst.1 v
    have hdiff:=card_difference_le_changed (B.filter (Hraw v)) (B.filter (H v))
    have habs:|((B.filter (Hraw v)).card:ℝ)-((B.filter (H v)).card:ℝ)|≤L:=hdiff.trans hchange
    have h1:=abs_lt.mp hh
    have h2:=abs_le.mp habs
    apply abs_le.mpr
    constructor <;> linarith
  · intro v w hvw hF
    have hfree:∀a∈({v,w}:Finset V),∀b∈({v,w}:Finset V),¬F.Adj a b:=by
      intro a ha b hb
      simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
      rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
      · exact fun h=>F.irrefl h
      · exact hF
      · exact fun h=>hF h.symm
      · exact fun h=>F.irrefl h
    have hh:=profile.columns {v,w} (by simp [hvw]) hfree
    have he:common B ({v,w}:Finset V) (fun x=>Finset.univ.filter (Hraw x))=
        B.filter (fun u=>Hraw v u∧Hraw w u):=by ext u;simp [mem_common_iff]
    rw [he,Finset.card_pair hvw] at hh
    have habs:=ordinary_boundary_hub_pair_count_stability Hraw H B v w L
      (profile.spoke_row_edit v) (profile.spoke_row_edit w)
    have h1:=abs_lt.mp hh
    have h2:=abs_le.mp habs
    apply abs_le.mpr
    constructor <;> linarith
end Oberwolfach
