module

public import Oberwolfach.MarkedReservedInnerRemainderTransfer

@[expose] public section
/-! The canonical inner arc set minus prescribed arcs is carried to the
canonical set in the reserved-deleted host by the actual deletion embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_reserved_canonical_inner_remainder
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
    let kh':=fun e:K'=>e.val.2
    let emb:=markedSampleDeletedArcsEmbedding P π d σ DR.edgeFinset;
    ∀ (DA:Finset (E⊕K)) (S:Finset (V×U)),
    (∀ z∈S,z.1∈I∧z.2∈J)→
    let A:=(Finset.univ.filter (fun a:E⊕K=>Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I))\DA
    let DA':=Finset.univ.filter (fun a:E'⊕K'=>emb a∈DA)
    let A':=(Finset.univ.filter (fun a:E'⊕K'=>Sum.elim t' kt' a∈I∧Sum.elim h' kh' a∈I))\DA';
    MarkedRemainderDivisible tail head ktail khead (H true) A S m→
    MarkedRemainderDivisible t' h' kt' kh' (H' true) A' S m ∧
      A'.image emb=A ∧
      (A'.image (fun a=>Sum.inl (markedPhysicalEdge t' h' kt' kh' π a))∪S.image Sum.inr)=
        (A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr):=by
  intro E K tail head ktail khead DR DS σ' H' E' K' t' h' kt' kh' emb DA S hS A DA' A' hdiv
  have hA:∀ a∈A,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I:=by
    intro a ha
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp ha).1).2
  obtain ⟨Anew,hpre,himage,hdivnew,hresources⟩:=marked_reserved_inner_remainder_transfer P π d m σ H C I J hI hC A S hA hS hdiv
  have hAeq:Anew=A':=by
    rw [hpre]
    ext a
    have hh:=markedSampleDeletedArcsEmbedding_endpoints_type P π d σ DR.edgeFinset a
    simp only [Finset.mem_filter,Finset.mem_univ,Finset.mem_sdiff,true_and,A,DA',A']
    rw [hh.1,hh.2.1]
  rw [hAeq] at hdivnew himage hresources
  exact ⟨hdivnew,himage,hresources⟩
end Oberwolfach
