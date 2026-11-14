module

public import Oberwolfach.MarkedCanonicalDeletedBalanceValues
public import Oberwolfach.MarkedFiniteResourcePreimages

@[expose] public section

/-! Identifying the resource set of a remaining host also identifies its
typed arc and spoke complements. Its exact divisibility then holds in
the canonical deleted sample, with no added balance hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_canonical_remainder_divisibility
    (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ) (σ : RawMarkedOutcome V U Γ Color)
    (H : Bool→V→U→Prop) :
    let E := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S := Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2);
    ∀ (FA AR : Finset (E⊕K)) (FS SR : Finset (V×U)),
    MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) AR SR m→
    markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π AR SR=
      markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π Finset.univ S\
      markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π FA FS→
    let σ' := rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ FA).edgeFinset
    let H' := markedDeletePhysicalSpokes H (markedFiniteSpokeGraph FS)
    let E' := MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K' := MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    AR=Finset.univ\FA ∧ SR=S\FS ∧
    MarkedRemainderDivisible (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ
      (Finset.univ.filter (fun s:V×U=>H' false s.1 s.2∨H' true s.1 s.2)) m := by
  intro E K S FA AR FS SR hdiv hRes σ' H' E' K'
  have hp := markedSampleArc_physical_injective P π (3*d) (fun e=>σ (Sum.inl e))
  rw [←markedFiniteResources_sdiff _ _ _ _ π hp Finset.univ FA S FS] at hRes
  obtain ⟨hA,hS⟩ := marked_finite_resources_determine_sets _ _ _ _ π hp AR (Finset.univ\FA) SR (S\FS) hRes
  refine ⟨hA,hS,?_⟩
  apply (markedFiniteBalance_eq_zero_iff _ _ _ _ _ _ _ _).mp
  intro z i
  rw [(marked_canonical_deleted_balance_values P π d m σ H FA FS Finset.univ Finset.univ z i).1]
  rw [←hA,←hS]
  exact (markedFiniteBalance_eq_zero_iff _ _ _ _ _ _ _ _).mpr hdiv z i

end Oberwolfach
