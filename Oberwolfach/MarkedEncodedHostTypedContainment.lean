module

public import Oberwolfach.MarkedHostRawEncoding

@[expose] public section

/-! The typed arcs of an encoded host are contained in the original sample
exactly when each supplied ordinary and marked arc occurs in that sample.
This condition concerns only actual physical rim arcs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K Γ Color : Type}
    [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_encoded_host_typed_containment_iff
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (tail head:E → V) (ktail khead:K → V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hE:∀ e,¬PermutationClose π (3*d) (tail e) (head e) ∧ P.Adj (tail e) (head e))
    (hK:∀ e,¬PermutationClose π (3*d) (ktail e) (khead e) ∧ P.Adj (ktail e) (π (khead e)))
    (σ:RawMarkedOutcome V U Γ Color) (I:Finset V) (hI:∀ v,π v∈I↔v∈I)
    (hAgree:∀ mark x y,x∈I → y∈I →
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
        (if mark then ∃ e:K,ktail e=x∧khead e=y else ∃ e:E,tail e=x∧head e=y))) :
    (∀ mark x y,markedPhysicalRim P π (3*d)
       (fun e=>rawMarkedEncodeHost tail head ktail khead π σ I (Sum.inl e)) mark x y=1 →
       markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1) ↔
    ((∀ e:E,markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) false (tail e) (head e)=1) ∧
     (∀ e:K,markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) true (ktail e) (khead e)=1)) := by
  constructor
  · intro hs
    constructor
    · intro e
      apply hs false (tail e) (head e)
      apply (rawMarkedEncodeHost_rims P π d tail head ktail khead hp hE hK σ I hI hAgree false (tail e) (head e)).mpr
      exact ⟨e,rfl,rfl⟩
    · intro e
      apply hs true (ktail e) (khead e)
      apply (rawMarkedEncodeHost_rims P π d tail head ktail khead hp hE hK σ I hI hAgree true (ktail e) (khead e)).mpr
      exact ⟨e,rfl,rfl⟩
  · rintro ⟨he,hk⟩ mark x y ht
    have hh := (rawMarkedEncodeHost_rims P π d tail head ktail khead hp hE hK σ I hI hAgree mark x y).mp ht
    cases mark with
    | false =>
      simp only [Bool.false_eq_true,↓reduceIte] at hh
      obtain ⟨e,rfl,rfl⟩ := hh
      exact he e
    | true =>
      simp only [↓reduceIte] at hh
      obtain ⟨e,rfl,rfl⟩ := hh
      exact hk e

/-- Agreement on the inner domain already supplies the sample membership of
inner arcs. Only supplied arcs outside that domain need further checking. -/
theorem marked_encoded_host_typed_containment_iff_outside
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (tail head:E → V) (ktail khead:K → V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hE:∀ e,¬PermutationClose π (3*d) (tail e) (head e) ∧ P.Adj (tail e) (head e))
    (hK:∀ e,¬PermutationClose π (3*d) (ktail e) (khead e) ∧ P.Adj (ktail e) (π (khead e)))
    (σ:RawMarkedOutcome V U Γ Color) (I:Finset V) (hI:∀ v,π v∈I↔v∈I)
    (hAgree:∀ mark x y,x∈I → y∈I →
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
        (if mark then ∃ e:K,ktail e=x∧khead e=y else ∃ e:E,tail e=x∧head e=y))) :
    (∀ mark x y,markedPhysicalRim P π (3*d)
       (fun e=>rawMarkedEncodeHost tail head ktail khead π σ I (Sum.inl e)) mark x y=1 →
       markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1) ↔
    ((∀ e:E,¬(tail e∈I ∧ head e∈I) →
       markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) false (tail e) (head e)=1) ∧
     (∀ e:K,¬(ktail e∈I ∧ khead e∈I) →
       markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) true (ktail e) (khead e)=1)) := by
  rw [marked_encoded_host_typed_containment_iff P π d tail head ktail khead hp hE hK σ I hI hAgree]
  constructor
  · rintro ⟨he,hk⟩
    exact ⟨fun e _=>he e,fun e _=>hk e⟩
  · rintro ⟨he,hk⟩
    constructor
    · intro e
      by_cases hi:tail e∈I ∧ head e∈I
      · exact (hAgree false (tail e) (head e) hi.1 hi.2).mpr ⟨e,rfl,rfl⟩
      · exact he e hi
    · intro e
      by_cases hi:ktail e∈I ∧ khead e∈I
      · exact (hAgree true (ktail e) (khead e) hi.1 hi.2).mpr ⟨e,rfl,rfl⟩
      · exact hk e hi

end Oberwolfach
