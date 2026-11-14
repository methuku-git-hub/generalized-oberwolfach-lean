module

public import Oberwolfach.MarkedReservedDeletionInnerAgreement
public import Oberwolfach.MarkedFiniteRemainderTransfer
public import Oberwolfach.MarkedSampleDeletionIncidences

@[expose] public section
/-! Divisible typed remainders inside the protected pair transfer exactly
when a disjoint reserved set is removed. Physical resources and types are
preserved, with no quotienting of arc multiplicities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reserved_inner_remainder_transfer
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (C:Finset (Finset V⊕(V×U))) (I:Finset V) (J:Finset U)
    (hI:∀ x,π x∈I↔x∈I) (hC:∀ e∈C,¬markedInnerResource I J e):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let DR:=physicalEdgeGraph (markedReservedRimPairs C)
    let DS:=markedFiniteSpokeGraph (markedReservedSpokePairs C)
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let t':=fun e:E'=>e.val.1
    let h':=fun e:E'=>e.val.2
    let kt':=fun e:K'=>e.val.1
    let kh':=fun e:K'=>e.val.2;
    ∀ (A:Finset (E⊕K)) (S:Finset (V×U)),
      (∀ a∈A,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)→
      (∀ z∈S,z.1∈I∧z.2∈J)→
      MarkedRemainderDivisible tail head ktail khead (H true) A S m→
    ∃ A':Finset (E'⊕K'),
      A'=Finset.univ.filter (fun a=>markedSampleDeletedArcsEmbedding P π d σ DR.edgeFinset a∈A) ∧
      A'.image (markedSampleDeletedArcsEmbedding P π d σ DR.edgeFinset)=A ∧
      MarkedRemainderDivisible t' h' kt' kh' (H' true) A' S m ∧
      (A'.image (fun a=>Sum.inl (markedPhysicalEdge t' h' kt' kh' π a))∪S.image Sum.inr)=
        (A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr) :=by
  intro E K tail head ktail khead DR DS σ' H' E' K' t' h' kt' kh' A S hA hS hdiv
  have hex (a:A):∃ a':E'⊕K',Sum.elim t' kt' a'=Sum.elim tail ktail a.val∧
      Sum.elim h' kh' a'=Sum.elim head khead a.val∧markedArcType a'=markedArcType a.val:=by
    have ha:=hA a.val a.property
    cases he:a.val with
    | inl e=>
      have ⟨e',he'⟩:=marked_reserved_deletion_preserves_inner_arcs P π d σ C I J hI hC false e
        (by simpa only [he,Sum.elim_inl] using ha.1) (by simpa only [he,Sum.elim_inl] using ha.2)
      refine ⟨Sum.inl e',?_,?_,?_⟩
      · simpa only [he,Sum.elim_inl] using congrArg Prod.fst he'
      · simpa only [he,Sum.elim_inl] using congrArg Prod.snd he'
      · simp only [he,markedArcType]
    | inr e=>
      have ⟨e',he'⟩:=marked_reserved_deletion_preserves_inner_arcs P π d σ C I J hI hC true e
        (by simpa only [he,Sum.elim_inr] using ha.1) (by simpa only [he,Sum.elim_inr] using ha.2)
      refine ⟨Sum.inr e',?_,?_,?_⟩
      · simpa only [he,Sum.elim_inr] using congrArg Prod.fst he'
      · simpa only [he,Sum.elim_inr] using congrArg Prod.snd he'
      · simp only [he,markedArcType]
  choose f hf hs ht using hex
  have hinj:Function.Injective f:=marked_finite_remainder_map_injective π
    (markedSampleArc_physical_injective P π (3*d) (fun a=>σ (Sum.inl a))) A f hf hs ht
  have hsp:∀ z∈S,H' true z.1 z.2↔H true z.1 z.2:=by
    intro z hz
    have hpair:=hS z hz
    have havoid:¬DS.Adj (Sum.inl z.1) (Sum.inr z.2):=
      (marked_reserved_graphs_avoid_internal_resources C I J hC).2 z.1 hpair.1 z.2 hpair.2
    simp [H',markedDeletePhysicalSpokes,havoid]
  let emb:=markedSampleDeletedArcsEmbedding P π d σ DR.edgeFinset
  have hp:=markedSampleArc_physical_injective P π (3*d) (fun a=>σ (Sum.inl a))
  have hback (a:A):emb (f a)=a.val:=by
    apply hp
    calc
      markedPhysicalEdge tail head ktail khead π (emb (f a))=
          markedPhysicalEdge t' h' kt' kh' π (f a):=by cases hfa:f a <;> rfl
      _ = markedPhysicalEdge tail head ktail khead π a.val:=
        marked_physical_edge_eq_of_endpoints_and_type π a.val (f a) (hf a) (hs a) (ht a)
  have himage:(Finset.univ.image f).image emb=A:=by
    ext a
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨b,⟨x,rfl⟩,rfl⟩
      rw [hback]
      exact x.property
    · intro ha
      exact ⟨f ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩,hback ⟨a,ha⟩⟩
  have hpre:Finset.univ.image f=Finset.univ.filter (fun a=>emb a∈A):=by
    ext a
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro ha
      rw [←himage]
      exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
    · intro ha
      rw [←himage] at ha
      obtain ⟨b,hb,hba⟩:=Finset.mem_image.mp ha
      have h:=emb.injective hba
      exact h ▸ hb
  have hdiv':=marked_finite_remainder_image_divisible A S f hinj hf hs ht hsp hdiv
  have heq:=marked_finite_remainder_image_resources π A S f hf hs ht
  exact ⟨Finset.univ.image f,hpre,himage,hdiv',heq⟩
end Oberwolfach
