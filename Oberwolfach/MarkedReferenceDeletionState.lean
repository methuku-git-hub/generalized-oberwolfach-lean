module

public import Oberwolfach.MarkedReindexedRemainder

@[expose] public section

/-! A vortex state records the actual deleted typed arcs and spoke pairs
of one fixed reference. Validity consists of exact divisibility and the two
specified incidence bounds, with no deletion in the next inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

structure MarkedReferenceDeletion (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) where
  arcs:Finset (MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false ⊕
    MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true)
  spokes:Finset (V×U)

namespace MarkedReferenceDeletion
variable {P:SimpleGraph V} {π:Equiv.Perm V} {d:ℕ} {σ:RawMarkedOutcome V U Γ Color}

def removed (D:MarkedReferenceDeletion P π d σ):Finset (Finset V⊕(V×U)):=
  markedFiniteResources (fun e=>e.val.1) (fun e=>e.val.2) (fun e=>e.val.1) (fun e=>e.val.2) π D.arcs D.spokes

def remaining (D:MarkedReferenceDeletion P π d σ) (H:Bool → V → U → Prop):Finset (Finset V⊕(V×U)):=
  markedFiniteResources (fun e:MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) false=>e.val.1) (fun e=>e.val.2)
    (fun e:MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) true=>e.val.1) (fun e=>e.val.2) π Finset.univ
    (Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2))\D.removed

def Valid (D:MarkedReferenceDeletion P π d σ) (H:Bool → V → U → Prop)
    (m:ℕ) (X:Finset V) (Y:Finset U) (γ σloss:ℝ):Prop:=
    let E:=MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) false
    let K:=MarkedSampleArc P π (3*d) (fun a=>σ (Sum.inl a)) true
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2);
    D.spokes⊆S ∧ D.removed.filter (markedInnerResource X Y)=∅ ∧
    (∀ physical z,(((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) physical z).filter
      (fun a=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) a∈D.removed)).card:ℝ)≤γ) ∧
    (∀ physical z,(((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) physical z).filter
      (fun a=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) a∈D.removed.filter (markedStarResource X Y))).card:ℝ)≤σloss) ∧
    let σNext:=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ D.arcs).edgeFinset
    let HNext:=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph D.spokes)
    let ENext:=MarkedSampleArc P π (3*d) (fun a=>σNext (Sum.inl a)) false
    let KNext:=MarkedSampleArc P π (3*d) (fun a=>σNext (Sum.inl a)) true;
    MarkedRemainderDivisible (fun e:ENext=>e.val.1) (fun e=>e.val.2)
      (fun e:KNext=>e.val.1) (fun e=>e.val.2) (HNext true) Finset.univ
      (Finset.univ.filter (fun z:V×U=>HNext false z.1 z.2∨HNext true z.1 z.2)) m

end MarkedReferenceDeletion

variable {V' U':Type} [Fintype V'] [Fintype U'] [LinearOrder V'] [DecidableEq U']

theorem marked_reindexed_remainder_state
    (f:V↪oV') (g:U↪U') (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool → V → U → Prop)
    (X:Finset V) (Y:Finset U) (F L:Finset (Finset V'⊕(V'×U'))) (γ σloss:ℝ)
    (h:MarkedReindexedRemainder f g P π d m σ H X Y F L γ σloss):
    ∃ D:MarkedReferenceDeletion P π d σ,
      D.Valid H m X Y γ σloss ∧
      D.removed.image (markedResourceEmbedding f.toEmbedding g)=F ∧
      (D.remaining H).image (markedResourceEmbedding f.toEmbedding g)=L := by
  obtain ⟨F₀,hF₀,FA,FS,hFS,hsets,himage,hremain,hempty,hbound,hstar,hdiv⟩:=h
  refine ⟨⟨FA,FS⟩,?_,?_,?_⟩
  · change _ ∧ _ ∧ _ ∧ _ ∧ _
    refine ⟨hFS,?_,?_,?_,hdiv⟩
    · simpa only [MarkedReferenceDeletion.removed,hsets] using hempty
    · simpa only [MarkedReferenceDeletion.removed,hsets] using hbound
    · simpa only [MarkedReferenceDeletion.removed,hsets] using hstar
  · simpa only [MarkedReferenceDeletion.removed,hsets] using himage
  · simpa only [MarkedReferenceDeletion.remaining,MarkedReferenceDeletion.removed,hsets] using hremain

end Oberwolfach
