module

public import Oberwolfach.MarkedReferenceDeletionComposition
public import Oberwolfach.MarkedReferenceStateRemainder

@[expose] public section
/-! A second small protected deletion can be added to a valid correction state;
its own physical cardinality pays for both incidence budgets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reference_incident_card_le_resources
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (C:Finset (Finset V⊕(V×U))) (physical:Bool) (z:V⊕U):
    let E:=MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) false
    let K:=MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) true;
    ((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
      π (H false) (H true) physical z).filter
      (fun e=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) e∈C)).card≤C.card := by
  intro E K
  let A:=(markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
      π (H false) (H true) physical z).filter
      (fun e=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) e∈C)
  let f:=markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
    (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true)
  have hi:Function.Injective f:=markedActivePhysical_injective (markedSampleArc_physical_injective P π (3*d) _)
  have hsub:A.image f⊆C:=by intro x hx;obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hx;exact (Finset.mem_filter.mp ha).2
  exact (Finset.card_image_of_injective A hi).symm.trans_le (Finset.card_le_card hsub)

theorem marked_reference_deletion_compose_valid
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (X:Finset V) (Y:Finset U) (γ₀ σ₀ γ₁ σ₁ e:ℝ)
    (D₀:MarkedReferenceDeletion P π d σ) (h₀:D₀.Valid H m X Y γ₀ σ₀):
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D₀.spokes);
    ∀ D₁:MarkedReferenceDeletion P π d σ', D₁.Valid H' m X Y γ₁ σ₁ →
      (D₁.removed.card:ℝ)≤e →
      (markedReferenceDeletionCompose P π d σ D₀ D₁).Valid H m X Y (γ₀+e) (σ₀+e) := by
  intro σ' H' D₁ h₁ he
  let D₂:=markedReferenceDeletionCompose P π d σ D₀ D₁
  have hRemoved:D₂.removed=D₀.removed∪D₁.removed:=marked_reference_deletion_compose_removed P π d σ D₀ D₁
  change _ ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨?_,?_,?_,?_,?_⟩
  · change D₀.spokes∪D₁.spokes⊆_
    apply Finset.union_subset h₀.1
    intro z hz
    have hh:=h₁.1 hz
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,markedDeletePhysicalSpokes] at hh ⊢
    exact hh.elim (fun h=>Or.inl h.1) (fun h=>Or.inr h.1)
  · rw [hRemoved,Finset.filter_union,h₀.2.1,h₁.2.1]
    simp
  · intro physical z
    let E:=MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) false
    let K:=MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) true
    let I:=markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) physical z
    let f:=markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true)
    change ((I.filter (fun a=>f a∈D₂.removed)).card:ℝ)≤γ₀+e
    rw [hRemoved]
    have hsub:I.filter (fun a=>f a∈D₀.removed∪D₁.removed)⊆
        I.filter (fun a=>f a∈D₀.removed) ∪ I.filter (fun a=>f a∈D₁.removed):=by
      intro a ha;simp only [Finset.mem_filter,Finset.mem_union] at ha ⊢;tauto
    have hc:=(Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hc':((I.filter (fun a=>f a∈D₀.removed∪D₁.removed)).card:ℝ)≤
        (I.filter (fun a=>f a∈D₀.removed)).card+(I.filter (fun a=>f a∈D₁.removed)).card:=by exact_mod_cast hc
    have hsmall:((I.filter (fun a=>f a∈D₁.removed)).card:ℝ)≤e:=by
      exact (Nat.cast_le.mpr (marked_reference_incident_card_le_resources P π d σ H D₁.removed physical z)).trans he
    have hbase:=h₀.2.2.1 physical z
    linarith
  · intro physical z
    let E:=MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) false
    let K:=MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) true
    let I:=markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) physical z
    let f:=markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true)
    change ((I.filter (fun a=>f a∈D₂.removed.filter (markedStarResource X Y))).card:ℝ)≤σ₀+e
    rw [hRemoved,Finset.filter_union]
    have hsub:I.filter (fun a=>f a∈D₀.removed.filter (markedStarResource X Y) ∪ D₁.removed.filter (markedStarResource X Y))⊆
        I.filter (fun a=>f a∈D₀.removed.filter (markedStarResource X Y)) ∪ I.filter (fun a=>f a∈D₁.removed.filter (markedStarResource X Y)):=by
      intro a ha;simp only [Finset.mem_filter,Finset.mem_union] at ha ⊢;tauto
    have hc:=(Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hc':((I.filter (fun a=>f a∈D₀.removed.filter (markedStarResource X Y) ∪ D₁.removed.filter (markedStarResource X Y))).card:ℝ)≤
        (I.filter (fun a=>f a∈D₀.removed.filter (markedStarResource X Y))).card+(I.filter (fun a=>f a∈D₁.removed.filter (markedStarResource X Y))).card:=by exact_mod_cast hc
    have hsmall:((I.filter (fun a=>f a∈D₁.removed.filter (markedStarResource X Y))).card:ℝ)≤e:=by
      have hh:=marked_reference_incident_card_le_resources P π d σ H (D₁.removed.filter (markedStarResource X Y)) physical z
      have hcard:((D₁.removed.filter (markedStarResource X Y)).card:ℝ)≤D₁.removed.card:=by exact_mod_cast Finset.card_filter_le _ _
      exact (Nat.cast_le.mpr hh).trans (hcard.trans he)
    have hbase:=h₀.2.2.2.1 physical z
    linarith
  · exact marked_reference_deletion_compose_divisible P π d m σ H X Y γ₁ σ₁ D₀ D₁ h₁

/-- A valid second deletion lies in the first remainder, so the two deleted
resource sets are disjoint and the composed remainder is exactly the second. -/
theorem marked_reference_deletion_compose_disjoint
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (X:Finset V) (Y:Finset U) (γ σloss:ℝ)
    (D₀:MarkedReferenceDeletion P π d σ):
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D₀.spokes);
    ∀ D₁:MarkedReferenceDeletion P π d σ', D₁.Valid H' m X Y γ σloss →
      D₁.removed⊆D₀.remaining H ∧ Disjoint D₀.removed D₁.removed ∧
      (markedReferenceDeletionCompose P π d σ D₀ D₁).remaining H=D₁.remaining H' := by
  intro σ' H' D₁ hvalid
  have hh:=D₁.removed_subset H' m X Y γ σloss hvalid
  have heq:=marked_deleted_sample_resources P π d σ H D₀.arcs D₀.spokes
  have hsub:D₁.removed⊆D₀.remaining H:=by
    dsimp only [MarkedReferenceDeletion.remaining,MarkedReferenceDeletion.removed]
    rw [←heq]
    exact hh
  refine ⟨hsub,?_,marked_reference_deletion_compose_remaining P π d σ H D₀ D₁⟩
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hmem:=hsub hy
  exact (Finset.mem_sdiff.mp hmem).2 hx
end Oberwolfach
