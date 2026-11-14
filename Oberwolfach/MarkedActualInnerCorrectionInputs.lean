module

public import Oberwolfach.MarkedInducedBalanceInputs
public import Oberwolfach.MarkedInducedOccurrenceMatrices
public import Oberwolfach.MarkedCanonicalDeletedBalanceValues
public import Oberwolfach.MarkedIterationBalancePreservation

@[expose] public section

/-! All eight inner-correction inputs in the actual remaining sample
follow from the fixed reference when the preceding deletion is empty on
the inner pair. The correction error is not increased by the star loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_actual_inner_balance_unchanged
    (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ) (σ : RawMarkedOutcome V U Γ Color)
    (H : Bool→V→U→Prop) (I : Finset V) (J : Finset U) (hI : ∀ v,π v∈I↔v∈I) :
    let E := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S := Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2);
    ∀ (KA : Finset (E⊕K)) (KS : Finset (V×U)),KS⊆S→
    (markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π KA KS).filter (markedInnerResource I J)=∅→
    let σ' := rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ KA).edgeFinset
    let H' := markedDeletePhysicalSpokes H (markedFiniteSpokeGraph KS)
    let E' := MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K' := MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let S' := Finset.univ.filter (fun s:V×U=>H' false s.1 s.2∨H' true s.1 s.2);
    ∀ z,Sum.elim (fun v=>v∈I) (fun u=>u∈J) z→∀ i,
      markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m I J z i=
      markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m I J z i := by
  intro E K S KA KS hKS hEmpty σ' H' E' K' S' z hz i
  have hKA : KA.filter (fun a=>Sum.elim (fun e:E=>e.val.1) (fun e:K=>e.val.1) a∈I∧
      Sum.elim (fun e:E=>e.val.2) (fun e:K=>e.val.2) a∈I)=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro a ha hin
    have hm : Sum.inl (markedPhysicalEdge (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π a)∈
        (markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π KA KS).filter (markedInnerResource I J) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩),
        (marked_physical_edge_inner_iff I hI a).mpr hin⟩
    rw [hEmpty] at hm
    exact Finset.notMem_empty _ hm
  have hKS' : KS.filter (fun s=>s.1∈I∧s.2∈J)=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro s hs hin
    have hm : Sum.inr s∈(markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π KA KS).filter (markedInnerResource I J) :=
      Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s,hs,rfl⟩),hin⟩
    rw [hEmpty] at hm
    exact Finset.notMem_empty _ hm
  rw [(marked_canonical_deleted_balance_values P π d m σ H KA KS I J z i).2,
    markedFiniteDomainBalance_sdiff _ _ _ _ _ Finset.univ KA S KS m I J (Finset.subset_univ _) hKS,
    markedFiniteDomainBalance_zero_inside_of_empty_induced _ _ _ _ _ KA KS m I J hKA hKS' z hz i,
    sub_zero]

theorem marked_actual_inner_correction_inputs
    (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ) (σ : RawMarkedOutcome V U Γ Color)
    (H : Bool→V→U→Prop) (hH : ∀ v u,¬(H false v u∧H true v u))
    (I : Finset V) (J : Finset U) (hI : ∀ v,π v∈I↔v∈I) (err δ h : ℝ)
    (hCutR : ∀ mark,BipartiteLargeCut
      (fun x:I=>fun y:I=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x.val y.val) δ h)
    (hCutS : ∀ mark,BipartiteLargeCut
      (relationMultiplicity (fun x:I=>fun u:J=>H mark x.val u.val)) δ h) :
    let E := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S := Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2);
    ∀ (KA : Finset (E⊕K)) (KS : Finset (V×U)),KS⊆S→
    (markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π KA KS).filter (markedInnerResource I J)=∅→
    (∀ z,Sum.elim (fun v=>v∈I) (fun u=>u∈J) z→∀ i,
      |markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m I J z i|≤err)→
    let σ' := rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ KA).edgeFinset
    let H' := markedDeletePhysicalSpokes H (markedFiniteSpokeGraph KS)
    let E' := MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K' := MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let EI := {e:E' // e.val.1∈I∧e.val.2∈I}
    let KI := {e:K' // e.val.1∈I∧e.val.2∈I}
    let tI := fun e:EI=>(⟨e.val.val.1,e.property.1⟩:I)
    let hI' := fun e:EI=>(⟨e.val.val.2,e.property.2⟩:I)
    let ktI := fun e:KI=>(⟨e.val.val.1,e.property.1⟩:I)
    let khI := fun e:KI=>(⟨e.val.val.2,e.property.2⟩:I)
    let H0I := fun v:I=>fun u:J=>H' false v.val u.val
    let HKI := fun v:I=>fun u:J=>H' true v.val u.val;
    (∀ v,|occurrenceDegree (Sum.elim tI ktI) v-
      (∑ u,if H0I v u then (1:ℝ) else 0)-(∑ u,if HKI v u then (1:ℝ) else 0)|≤err) ∧
    (∀ v,|occurrenceDegree (Sum.elim hI' khI) v-
      (∑ u,if H0I v u then (1:ℝ) else 0)-(∑ u,if HKI v u then (1:ℝ) else 0)|≤err) ∧
    (∀ v,|occurrenceDegree khI v-(∑ u,if HKI v u then (1:ℝ) else 0)|≤err) ∧
    (∀ u,|(∑ v,if H0I v u then (1:ℝ) else 0)-(m:ℝ)*(∑ v,if HKI v u then (1:ℝ) else 0)|≤err) ∧
    BipartiteLargeCut (occurrenceMultiplicity tI hI') δ h ∧
    BipartiteLargeCut (occurrenceMultiplicity ktI khI) δ h ∧
    BipartiteLargeCut (relationMultiplicity H0I) δ h ∧
    BipartiteLargeCut (relationMultiplicity HKI) δ h := by
  intro E K S KA KS hKS hEmpty hBal σ' H' E' K' EI KI tI hI' ktI khI H0I HKI
  have hH' : ∀ v u,¬(H' false v u∧H' true v u) := fun v u h=>hH v u ⟨h.1.1,h.2.1⟩
  obtain ⟨hb0,hb1,hbk,hbu⟩ := marked_induced_balance_inputs
    (fun e:E'=>e.val.1) (fun e=>e.val.2) (fun e:K'=>e.val.1) (fun e=>e.val.2)
    (H' false) (H' true) hH' I J m err (by
      intro z hz i
      rw [marked_actual_inner_balance_unchanged P π d m σ H I J hI KA KS hKS hEmpty z hz i]
      exact hBal z hz i)
  obtain ⟨hDR,hDS⟩ := marked_removed_resources_empty_inner P π d σ KA KS I J hEmpty
  have hr (mark:Bool) : BipartiteLargeCut
      (fun x:I=>fun y:I=>markedPhysicalRim P π (3*d) (fun e=>σ' (Sum.inl e)) mark x.val y.val) δ h := by
    rw [marked_induced_rim_matrix_unchanged P π d σ I hI _ hDR mark]
    exact hCutR mark
  have hs (mark:Bool) : (fun x:I=>fun u:J=>H' mark x.val u.val)=
      (fun x:I=>fun u:J=>H mark x.val u.val) := by
    funext x u
    simp only [H',markedDeletePhysicalSpokes,hDS x.val x.property u.val u.property,
      not_false_eq_true,and_true]
  refine ⟨hb0,hb1,hbk,hbu,?_,?_,?_,?_⟩
  · rw [markedSampleArc_induced_multiplicity]
    exact hr false
  · rw [markedSampleArc_induced_multiplicity]
    exact hr true
  · change BipartiteLargeCut (relationMultiplicity (fun x:I=>fun u:J=>H' false x.val u.val)) δ h
    rw [hs]
    exact hCutS false
  · change BipartiteLargeCut (relationMultiplicity (fun x:I=>fun u:J=>H' true x.val u.val)) δ h
    rw [hs]
    exact hCutS true

end Oberwolfach
