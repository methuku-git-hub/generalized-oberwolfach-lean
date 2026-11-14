module

public import Oberwolfach.MarkedHostPackingReindexing
public import Oberwolfach.MarkedHostReindexIncidences

@[expose] public section

/-! Transfer an actual cover-down packing through a typed host equivalence,
including its divisible supported remainder and both next-level bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K E' K':Type}
    [Fintype V] [Fintype U] [Fintype E] [Fintype K] [Fintype E'] [Fintype K']
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]
    [DecidableEq E'] [DecidableEq K']

theorem markedHostReindex_cover
    (tail head:E → V) (ktail khead:K → V) (tail' head':E' → V) (ktail' khead':K' → V)
    (H₀ HK:V → U → Prop) (π:Equiv.Perm V) (m b:ℕ) (e:E≃E') (k:K≃K')
    (ht:∀ a,tail' (e a)=tail a) (hh:∀ a,head' (e a)=head a)
    (hkt:∀ a,ktail' (k a)=ktail a) (hkh:∀ a,khead' (k a)=khead a)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hp':Function.Injective (markedPhysicalEdge tail' head' ktail' khead' π))
    (hH:∀ v u,¬(H₀ v u∧HK v u))
    (I T:Finset V) (J Q:Finset U) (hI:∀ v,π v∈I↔v∈I) (γ σ:ℝ) :
    let S:=Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)
    let B:=markedFiniteResources tail head ktail khead π Finset.univ S
    let B':=markedFiniteResources tail' head' ktail' khead' π Finset.univ S;
    MarkedRemainderDivisible tail' head' ktail' khead' HK Finset.univ S m →
    ∀ M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK),
    (∀ Y∈M,∀ Z∈M,Y≠Z → Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Z)) →
    let A:=Finset.univ\M.biUnion markedWheelArcs
    let Srem:=S\M.biUnion markedWheelSpokePairs
    let L:=markedFiniteResources tail head ktail khead π A Srem
    let F:=B.filter (markedInnerResource I J)\L;
    (∀ a∈A,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I) →
    (∀ s∈Srem,s.1∈I∧s.2∈J) →
    F.filter (markedInnerResource T Q)=∅ →
    (∀ physical z,(((markedIncidentEdges tail head ktail khead π H₀ HK physical z).filter
      (fun a=>markedActivePhysical tail head ktail khead π H₀ HK a∈F)).card:ℝ)≤γ) →
    (∀ physical z,(((markedIncidentEdges tail head ktail khead π H₀ HK physical z).filter
      (fun a=>markedActivePhysical tail head ktail khead π H₀ HK a∈F.filter (markedStarResource T Q))).card:ℝ)≤σ) →
    ∃ N:Finset (MarkedWheel tail' head' ktail' khead' m π b H₀ HK),
      (∀ Y∈N,∀ Z∈N,Y≠Z → Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Z)) ∧
      N.biUnion markedWheelPhysicalResources=M.biUnion markedWheelPhysicalResources ∧
      let A':=Finset.univ\N.biUnion markedWheelArcs
      let Srem':=S\N.biUnion markedWheelSpokePairs
      let L':=markedFiniteResources tail' head' ktail' khead' π A' Srem'
      let F':=B'.filter (markedInnerResource I J)\L';
      MarkedRemainderDivisible tail' head' ktail' khead' HK A' Srem' m ∧
      (∀ a∈A',Sum.elim tail' ktail' a∈I∧Sum.elim head' khead' a∈I) ∧
      (∀ s∈Srem',s.1∈I∧s.2∈J) ∧ L'=L ∧ F'=F ∧
      F'.filter (markedInnerResource T Q)=∅ ∧
      (∀ physical z,(((markedIncidentEdges tail' head' ktail' khead' π H₀ HK physical z).filter
        (fun a=>markedActivePhysical tail' head' ktail' khead' π H₀ HK a∈F')).card:ℝ)≤γ) ∧
      (∀ physical z,(((markedIncidentEdges tail' head' ktail' khead' π H₀ HK physical z).filter
        (fun a=>markedActivePhysical tail' head' ktail' khead' π H₀ HK a∈F'.filter (markedStarResource T Q))).card:ℝ)≤σ) := by
  intro S B B' hd M hM A Srem L F hA hS hDeep hInc hStar
  obtain ⟨N,hN,hRes,hdiv,hL⟩:=markedHostReindex_packing_remainder tail head ktail khead tail' head' ktail' khead'
    H₀ HK π m b e k ht hh hkt hkh hp hp' hH hd M hM
  have hsupport:∀ z∈markedFiniteResources tail' head' ktail' khead' π
      (Finset.univ\N.biUnion markedWheelArcs) (S\N.biUnion markedWheelSpokePairs),markedInnerResource I J z:=by
    rw [hL]
    exact (markedFiniteResources_support_iff tail head ktail khead π A Srem I J hI).mpr ⟨hA,hS⟩
  obtain ⟨hA',hS'⟩:=(markedFiniteResources_support_iff tail' head' ktail' khead' π
    (Finset.univ\N.biUnion markedWheelArcs) (S\N.biUnion markedWheelSpokePairs) I J hI).mp hsupport
  have hu:(Finset.univ:Finset (E⊕K)).image (e.toEmbedding.sumMap k.toEmbedding)=Finset.univ:=by
    apply Finset.image_univ_of_surjective
    intro a
    cases a with
    | inl a=>exact ⟨Sum.inl (e.symm a),by simp⟩
    | inr a=>exact ⟨Sum.inr (k.symm a),by simp⟩
  have hB:B'=B:=by
    have hh:=markedHostReindex_resources tail head ktail khead tail' head' ktail' khead' π e k ht hh hkt hkh Finset.univ S
    simpa only [hu] using hh
  have hF:B'.filter (markedInnerResource I J)\markedFiniteResources tail' head' ktail' khead' π
      (Finset.univ\N.biUnion markedWheelArcs) (S\N.biUnion markedWheelSpokePairs)=F:=by rw [hB,hL]
  have hFB:F⊆B:=Finset.sdiff_subset.trans (Finset.filter_subset _ _)
  refine ⟨N,hN,hRes,hdiv,hA',hS',hL,hF,?_,?_,?_⟩
  · rw [hF];exact hDeep
  · intro physical z
    rw [hF,markedHostReindex_incidence_card tail head ktail khead tail' head' ktail' khead'
      H₀ HK π e k ht hh hkt hkh hp' F hFB]
    exact hInc physical z
  · intro physical z
    rw [hF,markedHostReindex_incidence_card tail head ktail khead tail' head' ktail' khead'
      H₀ HK π e k ht hh hkt hkh hp' (F.filter (markedStarResource T Q)) ((Finset.filter_subset _ _).trans hFB)]
    exact hStar physical z

end Oberwolfach
