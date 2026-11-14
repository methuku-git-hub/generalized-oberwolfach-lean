module

public import Oberwolfach.MarkedReservedReducedHostDivisibility
public import Oberwolfach.MarkedReservedCanonicalFullRemainder

@[expose] public section
/-! Deleting the decomposable reserved set preserves global divisibility and
the canonical divisible inner remainder simultaneously. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
theorem marked_reserved_outer_and_inner_remainders_divisible
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
    let emb:=markedSampleDeletedArcsEmbedding P π d σ DR.edgeFinset
    let FullSpokes:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)
    let FullSpokes':=Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2)
    let R:=fun W:MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)=>markedWheelPhysicalResources W;
    (∀ v u,¬(H false v u∧H true v u))→
    MarkedRemainderDivisible tail head ktail khead (H true) Finset.univ FullSpokes m→
    HasResourceDecomposition R C→
    ∀ (DA:Finset (E⊕K)) (DS₀:Finset (V×U)),
    let S:=(Finset.univ.filter (fun z:V×U=>(H false z.1 z.2∨H true z.1 z.2)∧z.1∈I∧z.2∈J))\DS₀
    let S':=(Finset.univ.filter (fun z:V×U=>(H' false z.1 z.2∨H' true z.1 z.2)∧z.1∈I∧z.2∈J))\DS₀;
    let A:=(Finset.univ.filter (fun a:E⊕K=>Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I))\DA
    let DA':=Finset.univ.filter (fun a:E'⊕K'=>emb a∈DA)
    let A':=(Finset.univ.filter (fun a:E'⊕K'=>Sum.elim t' kt' a∈I∧Sum.elim h' kh' a∈I))\DA';
    MarkedRemainderDivisible tail head ktail khead (H true) A S m→
    MarkedRemainderDivisible t' h' kt' kh' (H' true) Finset.univ FullSpokes' m ∧
    MarkedRemainderDivisible t' h' kt' kh' (H' true) A' S' m ∧
      A'.image emb=A ∧
      (A'.image (fun a=>Sum.inl (markedPhysicalEdge t' h' kt' kh' π a))∪S'.image Sum.inr)=
        (A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr):=by
  intro E K tail head ktail khead DR DS σ' H' E' K' t' h' kt' kh' emb FullSpokes FullSpokes' R hH hOuter hDec
    DA DS₀ S S' A DA' A' hInner
  have hOuter':=marked_reserved_reduced_host_divisible P π d m σ H hH hOuter C hDec
  have hInner':=marked_reserved_canonical_full_inner_remainder P π d m σ H C I J hI hC DA DS₀ hInner
  exact ⟨hOuter',hInner'⟩
end Oberwolfach
