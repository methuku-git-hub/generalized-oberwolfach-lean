module

public import Oberwolfach.MarkedRawHostArcEquivalences
public import Oberwolfach.MarkedHostReindexing

@[expose] public section

/-! Exact finite resource, balance and decomposition statements for a
modified host encoded in raw coordinates. No random law is assigned to
the encoded outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K Γ Color:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_encoded_host_invariants
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (tail head:E → V) (ktail khead:K → V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hE:∀ e,¬PermutationClose π (3*d) (tail e) (head e)∧P.Adj (tail e) (head e))
    (hK:∀ e,¬PermutationClose π (3*d) (ktail e) (khead e)∧P.Adj (ktail e) (π (khead e)))
    (σ:RawMarkedOutcome V U Γ Color) (I:Finset V) (hI:∀ v,π v∈I↔v∈I)
    (hAgree:∀ mark x y,x∈I → y∈I →
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
        (if mark then ∃ e:K,ktail e=x∧khead e=y else ∃ e:E,tail e=x∧head e=y)))
    (H:Bool → V → U → Prop) (m:ℕ) :
    let τ:=rawMarkedEncodeHost tail head ktail khead π σ I
    let E':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true
    let tail':=fun e:E'=>e.val.1
    let head':=fun e:E'=>e.val.2
    let ktail':=fun e:K'=>e.val.1
    let khead':=fun e:K'=>e.val.2
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2);
    markedFiniteResources tail' head' ktail' khead' π Finset.univ S=
      markedFiniteResources tail head ktail khead π Finset.univ S ∧
    (∀ z i,markedFiniteBalance tail' head' ktail' khead' (H true) Finset.univ S m z i=
      markedFiniteBalance tail head ktail khead (H true) Finset.univ S m z i) ∧
    (∀ X Z z i,markedFiniteDomainBalance tail' head' ktail' khead' (H true) Finset.univ S m X Z z i=
      markedFiniteDomainBalance tail head ktail khead (H true) Finset.univ S m X Z z i) ∧
    (MarkedRemainderDivisible tail' head' ktail' khead' (H true) Finset.univ S m ↔
      MarkedRemainderDivisible tail head ktail khead (H true) Finset.univ S m) ∧
    (∀ R:Finset (Finset V⊕(V×U)),
      HasResourceDecomposition (fun W:MarkedWheel tail' head' ktail' khead' m π (3*d) (H false) (H true)=>markedWheelPhysicalResources W) R ↔
      HasResourceDecomposition (fun W:MarkedWheel tail head ktail khead m π (3*d) (H false) (H true)=>markedWheelPhysicalResources W) R) := by
  intro τ E' K' tail' head' ktail' khead' S
  let e:E≃E':=markedRawHostOrdinaryArcEquiv P π d tail head ktail khead hp hE hK σ I hI hAgree
  let k:K≃K':=markedRawHostMarkedArcEquiv P π d tail head ktail khead hp hE hK σ I hI hAgree
  have ht:∀ a,tail' (e a)=tail a:=fun _=>rfl
  have hh:∀ a,head' (e a)=head a:=fun _=>rfl
  have hkt:∀ a,ktail' (k a)=ktail a:=fun _=>rfl
  have hkh:∀ a,khead' (k a)=khead a:=fun _=>rfl
  have hu:(Finset.univ:Finset (E⊕K)).image (e.toEmbedding.sumMap k.toEmbedding)=Finset.univ := by
    apply Finset.image_univ_of_surjective
    intro a
    cases a with
    | inl a=>exact ⟨Sum.inl (e.symm a),by simp⟩
    | inr a=>exact ⟨Sum.inr (k.symm a),by simp⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [hu] using markedHostReindex_resources tail head ktail khead tail' head' ktail' khead' π e k ht hh hkt hkh Finset.univ S
  · intro z i
    simpa only [hu] using markedHostReindex_balance tail head ktail khead tail' head' ktail' khead' (H true) (H true)
      e k ht hh hkt hkh Finset.univ S m (fun _ _=>Iff.rfl) z i
  · intro X Z z i
    simpa only [hu] using markedHostReindex_domain_balance tail head ktail khead tail' head' ktail' khead' (H true) (H true)
      e k ht hh hkt hkh Finset.univ S m (fun _ _=>Iff.rfl) X Z z i
  · simpa only [hu] using markedHostReindex_divisible_iff tail head ktail khead tail' head' ktail' khead' (H true) (H true)
      e k ht hh hkt hkh Finset.univ S m (fun _ _=>Iff.rfl)
  · exact markedHostReindex_decomposition_iff tail head ktail khead tail' head' ktail' khead'
      (H false) (H true) π m (3*d) e k ht hh hkt hkh

end Oberwolfach
