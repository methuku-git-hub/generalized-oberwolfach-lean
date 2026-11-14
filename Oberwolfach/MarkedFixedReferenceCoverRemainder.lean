module

public import Oberwolfach.MarkedDeletedHostIncidence

@[expose] public section

/-! Exact restoration of the fixed reference on the next inner pair.
An earlier deletion is empty on that pair, so the next error consists
only of the resources consumed there by the current covering packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem fixed_reference_after_cover
    {R : Type*} [DecidableEq R] (B E L : Finset R) (p : R→Prop)
    (hE : E.filter p=∅) (hL : L⊆(B\E).filter p) :
    (B\E).filter p=B.filter p ∧
    ((B\E).filter p\L)=B.filter p\L ∧
    L=B.filter p\(B.filter p\L) ∧ (B.filter p\L)⊆B\E := by
  have h : (B\E).filter p=B.filter p := by
    ext e
    have he : e∈E→¬p e := by
      intro he hp
      have hf : e∈E.filter p := Finset.mem_filter.mpr ⟨he,hp⟩
      rw [hE] at hf
      exact Finset.notMem_empty _ hf
    simp only [Finset.mem_filter,Finset.mem_sdiff]
    tauto
  have hL' : L⊆B.filter p := h ▸ hL
  refine ⟨h,by rw [h],?_,?_⟩
  · ext e
    have he := fun he=>hL' (x:=e) he
    simp only [Finset.mem_sdiff] at *
    tauto
  · rw [←h]
    exact Finset.sdiff_subset.trans (Finset.filter_subset _ _)

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_cover_remainder_fixed_reference
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (σ : RawMarkedOutcome V U Γ Color)
    (H : Bool→V→U→Prop) :
    let E := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true;
    ∀ (KA : Finset (E⊕K)) (KS : Finset (V×U)),
    let DR := markedSampleArcSetGraph P π d σ KA
    let DS := markedFiniteSpokeGraph KS
    let σ' := rawMarkedDeleteRims σ DR.edgeFinset
    let H' := markedDeletePhysicalSpokes H DS
    let E' := MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K' := MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let B := markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π Finset.univ
      (Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2))
    let B' := markedFiniteResources (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) π Finset.univ
      (Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2));
    ∀ (I T : Finset V) (J Z : Finset U) (L : Finset (Finset V⊕(V×U))) (γ σloss : ℝ),
    (markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π KA KS).filter (markedInnerResource I J)=∅→
    L⊆B'.filter (markedInnerResource I J)→
    let removed := B'.filter (markedInnerResource I J)\L;
    removed.filter (markedInnerResource T Z)=∅→
    (∀ physical x,(((markedIncidentEdges (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) π (H' false) (H' true) physical x).filter
      (fun e=>markedActivePhysical (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) π (H' false) (H' true) e∈removed)).card:ℝ)≤γ)→
    (∀ physical x,(((markedIncidentEdges (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) π (H' false) (H' true) physical x).filter
      (fun e=>markedActivePhysical (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) π (H' false) (H' true) e∈removed.filter (markedStarResource T Z))).card:ℝ)≤σloss)→
    ∃ F : Finset (Finset V⊕(V×U)),
      F=removed ∧ L=B.filter (markedInnerResource I J)\F ∧
      F⊆B'.filter (markedInnerResource I J) ∧ F.filter (markedInnerResource T Z)=∅ ∧
      (∀ physical x,(((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) physical x).filter
        (fun e=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
          (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) e∈F)).card:ℝ)≤γ) ∧
      (∀ physical x,(((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) physical x).filter
        (fun e=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
          (fun e:K=>e.val.1) (fun e=>e.val.2) π (H false) (H true) e∈F.filter (markedStarResource T Z))).card:ℝ)≤σloss) := by
  intro E K KA KS DR DS σ' H' E' K' B B' I T J Z L γ σloss hEmpty hL removed hDeep hInc hStar
  let R := markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
    (fun e:K=>e.val.1) (fun e=>e.val.2) π KA KS
  have hB : B'=B\R := marked_deleted_sample_resources P π d σ H KA KS
  have hL' : L⊆(B\R).filter (markedInnerResource I J) := hB ▸ hL
  obtain ⟨hInner,_,hRest,_⟩ := fixed_reference_after_cover B R L (markedInnerResource I J) hEmpty hL'
  have hInner' : B'.filter (markedInnerResource I J)=B.filter (markedInnerResource I J) := by rwa [hB]
  have hRemoved : removed=B.filter (markedInnerResource I J)\L := by dsimp [removed];rw [hInner']
  have hRemovedB : removed⊆B' := Finset.sdiff_subset.trans (Finset.filter_subset _ _)
  refine ⟨removed,rfl,?_,Finset.sdiff_subset,hDeep,?_,?_⟩
  · rw [hRemoved]
    exact hRest
  · intro physical x
    rw [marked_deleted_host_incidence_card P π d σ H DR DS removed hRemovedB physical x]
    exact hInc physical x
  · intro physical x
    rw [marked_deleted_host_incidence_card P π d σ H DR DS
      (removed.filter (markedStarResource T Z)) ((Finset.filter_subset _ _).trans hRemovedB) physical x]
    exact hStar physical x

end Oberwolfach
