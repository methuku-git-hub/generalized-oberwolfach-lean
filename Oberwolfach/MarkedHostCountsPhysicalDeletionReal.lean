module

public import Oberwolfach.MarkedHostCountsPhysicalDeletion
public import Oberwolfach.MarkedProfileMonotonicity

@[expose] public section

/-! Degree bounds may be real. Taking the floor introduces no additive
loss because the deleted degrees are integers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_sample_host_extensions_after_physical_deletion_real
    (P:SimpleGraph V) (π:Equiv.Perm V) (d l:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (c ch delta:ℝ) (hdelta:0≤delta)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hrim:∀ v,(DR.degree v:ℝ)≤delta) (hspoke:∀ z,(DS.degree z:ℝ)≤delta) :
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    MarkedHostExtensionCounts (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H false) (H true) π (3*d) l c ch →
    MarkedHostExtensionCounts (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' false) (H' true) π (3*d) l
      (c-4*delta) (ch-(l+11)*delta) := by
  intro E K σ' H' E' K' Q
  let t:=⌊delta⌋₊
  have ht:(t:ℝ)≤delta:=Nat.floor_le hdelta
  have hR:∀ v,DR.degree v≤t:=by intro v;exact Nat.le_floor (hrim v)
  have hS:∀ z,DS.degree z≤t:=by intro z;exact Nat.le_floor (hspoke z)
  have hh:=marked_sample_host_extensions_after_physical_deletion P π d l σ H c ch DR DS t hR hS Q
  exact hh.lowerBounds (by linarith only [ht]) (by
    have hl:0≤((l+11:ℕ):ℝ):=by positivity
    nlinarith only [ht,hl,mul_nonneg (sub_nonneg.mpr ht) hl])

end Oberwolfach
