module

public import Oberwolfach.MarkedEndpointArcExhaustion
public import Oberwolfach.MarkedRowRequiredResources
public import Oberwolfach.MarkedActualRowResources
public import Oberwolfach.MarkedRowCoverPackings

@[expose] public section

/-! The required resource set in a sampled row cover is exactly the set
of its actual incident arc occurrences and root spokes. Incoming marked
arcs retain their auxiliary head and their shifted physical endpoint. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_sample_row_required_iff
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (v:V) (r:Finset V⊕(V×U)):
    let tail:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1
    let head:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.2
    let ktail:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1
    let khead:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.2
    let ain:=markedEndpointTaggedArcEmbedding P π d Finset.univ true v σ
    let xout:=markedEndpointTaggedArcEmbedding P π d Finset.univ false v σ
    r∈markedRowRequiredResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (π:=π)
      ain xout v ((Finset.univ.filter (H false v))∪(Finset.univ.filter (H true v))) ↔
      (∃ a,(Sum.elim head khead a=v∨Sum.elim tail ktail a=v)∧
        Sum.inl (markedPhysicalEdge tail head ktail khead π a)=r)∨
      (∃ u:U,(H false v u∨H true v u)∧Sum.inr (v,u)=r):=by
  dsimp only
  simp only [markedRowRequiredResources,Finset.mem_union,Finset.mem_image,
    Finset.mem_univ,true_and,Finset.mem_filter]
  constructor
  · rintro ((⟨a,ha⟩|⟨a,ha⟩)|⟨u,hu,hr⟩)
    · exact Or.inl ⟨_,Or.inl (marked_endpoint_arc_embedding_head P π d Finset.univ true v σ a),ha⟩
    · exact Or.inl ⟨_,Or.inr (marked_endpoint_arc_embedding_tail P π d Finset.univ false v σ a),ha⟩
    · exact Or.inr ⟨u,hu,hr⟩
  · rintro (⟨a,ha,hr⟩|⟨u,hu,hr⟩)
    · rcases ha with ha|ha
      · obtain ⟨x,hx⟩:=marked_endpoint_tagged_arc_embedding_exhaustive P π d Finset.univ true v σ a ha (Finset.mem_univ _)
        exact Or.inl (Or.inl ⟨x,by rw [hx];exact hr⟩)
      · obtain ⟨x,hx⟩:=marked_endpoint_tagged_arc_embedding_exhaustive P π d Finset.univ false v σ a ha (Finset.mem_univ _)
        exact Or.inl (Or.inr ⟨x,by rw [hx];exact hr⟩)
    · exact Or.inr ⟨u,hu,hr⟩


theorem marked_sample_row_covers_cover_star
    (P:SimpleGraph V) (π:Equiv.Perm V) (d l n K:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (F T:Finset V) (v:Fin n→V)
    (hTv:T⊆Finset.univ.image v) (hT:∀ x,π x∈T↔x∈T):
    let tail:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1
    let head:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.2
    let ktail:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1
    let khead:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.2
    ∀ C:Fin n→Finset (MarkedWheel tail head ktail khead (l+3) π (3*d) (H false) (H true)),
    (∀ i,MarkedRowCover (C i) (v i) F
      (markedRowRequiredResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (π:=π)
        (markedEndpointTaggedArcEmbedding P π d Finset.univ true (v i) σ)
        (markedEndpointTaggedArcEmbedding P π d Finset.univ false (v i) σ)
        (v i) ((Finset.univ.filter (H false (v i)))∪(Finset.univ.filter (H true (v i)))))
      ((Finset.univ.filter (H false (v i)))∪(Finset.univ.filter (H true (v i)))) K)→
    let M:=(Finset.univ.biUnion C).biUnion markedWheelPhysicalResources
    (∀ a,markedStarResource T (∅:Finset U) (Sum.inl (markedPhysicalEdge tail head ktail khead π a))→
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈M) ∧
    (∀ x u,(H false x u∨H true x u)→x∈T→Sum.inr (x,u)∈M):=by
  dsimp only
  intro C hC
  have hrow (i:Fin n) (r:Finset V⊕(V×U))
      (hr:r∈markedRowRequiredResources
        (tail:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (head:=fun e=>e.val.2)
        (ktail:=fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (khead:=fun e=>e.val.2) (π:=π)
        (markedEndpointTaggedArcEmbedding P π d Finset.univ true (v i) σ)
        (markedEndpointTaggedArcEmbedding P π d Finset.univ false (v i) σ)
        (v i) ((Finset.univ.filter (H false (v i)))∪(Finset.univ.filter (H true (v i))))):
      r∈(Finset.univ.biUnion C).biUnion markedWheelPhysicalResources:=by
    obtain ⟨W,hW,hrW⟩:=Finset.mem_biUnion.mp ((hC i).covers hr)
    exact Finset.mem_biUnion.mpr ⟨W,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hW⟩,hrW⟩
  constructor
  · intro a ha
    have hi:∃ i,Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) a=v i∨
        Sum.elim (fun e=>e.val.1) (fun e=>e.val.1) a=v i:=by
      rcases (marked_physical_rim_star_iff _ _ _ _ π T (∅:Finset U) hT a).mp ha with hx|hx
      · obtain ⟨i,_,hi⟩:=Finset.mem_image.mp (hTv hx)
        exact ⟨i,Or.inr hi.symm⟩
      · obtain ⟨i,_,hi⟩:=Finset.mem_image.mp (hTv hx)
        exact ⟨i,Or.inl hi.symm⟩
    obtain ⟨i,hi⟩:=hi
    exact hrow i _ ((marked_sample_row_required_iff P π d σ H (v i) _).mpr (Or.inl ⟨a,hi,rfl⟩))
  · intro x u hH hx
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp (hTv hx)
    subst x
    exact hrow i _ ((marked_sample_row_required_iff P π d σ H (v i) _).mpr (Or.inr ⟨u,hH,rfl⟩))

end Oberwolfach
