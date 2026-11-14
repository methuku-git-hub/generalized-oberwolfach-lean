module

public import Oberwolfach.MarkedReferenceDeletionState
public import Oberwolfach.MarkedSampleDeletionIncidences
public import Oberwolfach.MarkedDeletedSampleResources
public import Oberwolfach.MarkedPhysicalDeletionComposition

@[expose] public section
/-! Successive deletions of the corrected sample lift to one deletion of the
original reference, with exactly the union of the physical resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

noncomputable def markedReferenceDeletionCompose
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (D₀:MarkedReferenceDeletion P π d σ):
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset;
    MarkedReferenceDeletion P π d σ' → MarkedReferenceDeletion P π d σ := by
  intro σ' D₁
  exact ⟨D₀.arcs ∪ D₁.arcs.image (markedSampleDeletedArcsEmbedding P π d σ
    (markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset), D₀.spokes∪D₁.spokes⟩

theorem marked_reference_deletion_compose_removed
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (D₀:MarkedReferenceDeletion P π d σ):
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset;
    ∀ D₁:MarkedReferenceDeletion P π d σ',
      (markedReferenceDeletionCompose P π d σ D₀ D₁).removed=D₀.removed∪D₁.removed := by
  intro σ' D₁
  let emb:=markedSampleDeletedArcsEmbedding P π d σ (markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset
  have hm:(D₁.arcs.image emb).image (fun a=>(Sum.inl (markedPhysicalEdge
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2) π a) : Finset V⊕(V×U))) =
      D₁.arcs.image (fun a=>(Sum.inl (markedPhysicalEdge
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2) π a) : Finset V⊕(V×U))):=by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro a ha
    cases a <;> rfl
  dsimp only [emb] at hm
  simp only [MarkedReferenceDeletion.removed,markedReferenceDeletionCompose,markedFiniteResources,
    Finset.image_union,hm]
  ac_rfl

theorem marked_reference_deletion_compose_remaining
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (D₀:MarkedReferenceDeletion P π d σ):
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D₀.spokes);
    ∀ D₁:MarkedReferenceDeletion P π d σ',
      (markedReferenceDeletionCompose P π d σ D₀ D₁).remaining H=D₁.remaining H' := by
  intro σ' H' D₁
  have heq:=marked_deleted_sample_resources P π d σ H D₀.arcs D₀.spokes
  simp only [MarkedReferenceDeletion.remaining,marked_reference_deletion_compose_removed]
  rw [heq]
  ext e
  simp only [Finset.mem_sdiff,Finset.mem_union]
  tauto

/-- The composed deletion has exactly the two successive physical samples. -/
theorem marked_reference_deletion_compose_samples
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (D₀:MarkedReferenceDeletion P π d σ):
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D₀.spokes);
    ∀ D₁:MarkedReferenceDeletion P π d σ',
      let D₂:=markedReferenceDeletionCompose P π d σ D₀ D₁;
      rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ D₂.arcs).edgeFinset =
        rawMarkedDeleteRims σ' (markedSampleArcSetGraph P π d σ' D₁.arcs).edgeFinset ∧
      markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D₂.spokes) =
        markedDeletePhysicalSpokes H' (markedFiniteSpokeGraph D₁.spokes) := by
  intro σ' H' D₁ D₂
  let emb:=markedSampleDeletedArcsEmbedding P π d σ (markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset
  have hgraph:markedSampleArcSetGraph P π d σ (D₁.arcs.image emb)=markedSampleArcSetGraph P π d σ' D₁.arcs:=by
    dsimp only [markedSampleArcSetGraph]
    congr 1
    rw [Finset.image_image]
    apply Finset.image_congr
    intro a ha
    cases a <;> rfl
  constructor
  · change rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ (D₀.arcs∪D₁.arcs.image emb)).edgeFinset = _
    rw [markedSampleArcSetGraph_union,hgraph]
    convert (rawMarkedDeleteRims_sup σ (markedSampleArcSetGraph P π d σ D₀.arcs)
      (markedSampleArcSetGraph P π d σ' D₁.arcs)).symm using 1 <;> congr 5 <;> first | rfl | exact Subsingleton.elim _ _
  · change markedDeletePhysicalSpokes H (markedFiniteSpokeGraph (D₀.spokes∪D₁.spokes)) = _
    rw [markedFiniteSpokeGraph_union,←markedDeletePhysicalSpokes_sup]

/-- Exact divisibility survives when a valid second deletion is lifted to
the original sample. -/
theorem marked_reference_deletion_compose_divisible
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (X:Finset V) (Y:Finset U) (γ σloss:ℝ)
    (D₀:MarkedReferenceDeletion P π d σ):
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ D₀.arcs).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D₀.spokes);
    ∀ D₁:MarkedReferenceDeletion P π d σ', D₁.Valid H' m X Y γ σloss →
    let D₂:=markedReferenceDeletionCompose P π d σ D₀ D₁
    let σ₂:=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ D₂.arcs).edgeFinset
    let H₂:=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D₂.spokes)
    let E₂:=MarkedSampleArc P π (3*d) (fun e=>σ₂ (Sum.inl e)) false
    let K₂:=MarkedSampleArc P π (3*d) (fun e=>σ₂ (Sum.inl e)) true;
    MarkedRemainderDivisible (fun e:E₂=>e.val.1) (fun e=>e.val.2) (fun e:K₂=>e.val.1) (fun e=>e.val.2)
      (H₂ true) Finset.univ (Finset.univ.filter (fun z:V×U=>H₂ false z.1 z.2∨H₂ true z.1 z.2)) m := by
  intro σ' H' D₁ hvalid D₂ σ₂ H₂ E₂ K₂
  have heq:=marked_reference_deletion_compose_samples P π d σ H D₀ D₁
  dsimp only at heq
  let Div (τ:RawMarkedOutcome V U Γ Color) (J:Bool→V→U→Prop):Prop :=
    let E:=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true;
    MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
      (J true) Finset.univ (Finset.univ.filter (fun z:V×U=>J false z.1 z.2∨J true z.1 z.2)) m
  have hh:Div (rawMarkedDeleteRims σ' (markedSampleArcSetGraph P π d σ' D₁.arcs).edgeFinset)
      (markedDeletePhysicalSpokes H' (markedFiniteSpokeGraph D₁.spokes)):=hvalid.2.2.2.2
  have heqdiv:=congrArg₂ Div heq.1 heq.2
  change Div σ₂ H₂
  exact heqdiv.mpr hh
end Oberwolfach
