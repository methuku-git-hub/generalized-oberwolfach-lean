module

public import Oberwolfach.MarkedReservedDeletionInnerAgreement
public import Oberwolfach.MarkedSampleDeletionIncidences

@[expose] public section
/-! Every finite typed arc set inside the protected pair lifts exactly to
the absorber-deleted sample, without a divisibility assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reserved_inner_arc_set_lift
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (C:Finset (Finset V⊕(V×U))) (I:Finset V) (J:Finset U)
    (hI:∀ x,π x∈I↔x∈I) (hC:∀ e∈C,¬markedInnerResource I J e):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let DR:=physicalEdgeGraph (markedReservedRimPairs C)
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let emb:=markedSampleDeletedArcsEmbedding P π d σ DR.edgeFinset;
    ∀ A:Finset (E⊕K),
    (∀ a∈A,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)→
    let A':=Finset.univ.filter (fun a:E'⊕K'=>emb a∈A);
    A'.image emb=A ∧ A'.card=A.card :=by
  intro E K tail head ktail khead DR σ' E' K' emb A hA A'
  have hsurvive:∀ a∈A,∃ a':E'⊕K',emb a'=a:=by
    intro a ha
    have hh:=hA a ha
    cases haType:a with
    | inl e=>
      obtain ⟨e',he'⟩:=marked_reserved_deletion_preserves_inner_arcs P π d σ C I J hI hC false e
        (by simpa only [haType,Sum.elim_inl] using hh.1) (by simpa only [haType,Sum.elim_inl] using hh.2)
      refine ⟨Sum.inl e',?_⟩
      apply congrArg Sum.inl
      apply Subtype.ext
      exact he'
    | inr e=>
      obtain ⟨e',he'⟩:=marked_reserved_deletion_preserves_inner_arcs P π d σ C I J hI hC true e
        (by simpa only [haType,Sum.elim_inr] using hh.1) (by simpa only [haType,Sum.elim_inr] using hh.2)
      refine ⟨Sum.inr e',?_⟩
      apply congrArg Sum.inr
      apply Subtype.ext
      exact he'
  have himage:A'.image emb=A:=by
    ext a
    constructor
    · intro ha
      obtain ⟨a',ha',rfl⟩:=Finset.mem_image.mp ha
      exact (Finset.mem_filter.mp ha').2
    · intro ha
      obtain ⟨a',he⟩:=hsurvive a ha
      exact Finset.mem_image.mpr ⟨a',Finset.mem_filter.mpr ⟨Finset.mem_univ _,he.symm ▸ ha⟩,he⟩
  exact ⟨himage,(Finset.card_image_of_injective A' emb.injective).symm.trans (congrArg Finset.card himage)⟩
end Oberwolfach
