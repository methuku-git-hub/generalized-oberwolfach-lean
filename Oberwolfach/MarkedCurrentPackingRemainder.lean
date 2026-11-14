module

public import Oberwolfach.MarkedCanonicalDeletedPacking
public import Oberwolfach.MarkedCanonicalDeletedBalanceValues
public import Oberwolfach.MarkedDeletedSampleResources

@[expose] public section

/-! Lift the actual packing in the current deleted sample to the original
occurrence identifiers and compute its remaining typed host. Divisibility
is taken from the current host, not from the fixed reference or its earlier
deleted edge set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_current_packing_original_remainder
    (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ) (σ : RawMarkedOutcome V U Γ Color)
    (H : Bool→V→U→Prop) (hH : ∀ v u,¬(H false v u∧H true v u)) :
    let E := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S := Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2);
    ∀ (KA : Finset (E⊕K)) (KS : Finset (V×U)),
    let DR := markedSampleArcSetGraph P π d σ KA
    let DS := markedFiniteSpokeGraph KS
    let σ' := rawMarkedDeleteRims σ DR.edgeFinset
    let H' := markedDeletePhysicalSpokes H DS
    let E' := MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K' := MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let S' := Finset.univ.filter (fun s:V×U=>H' false s.1 s.2∨H' true s.1 s.2);
    MarkedRemainderDivisible (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m→
    ∀ M : Finset (MarkedPhysicalDeletedSampleWheel P π d m σ DR DS H),
    (∀ Y∈M,∀ Z∈M,Y≠Z→Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Z))→
    let N := M.image (markedPhysicalDeletedSampleWheelLift P π d m σ DR DS H)
    let AR := Finset.univ\(KA∪N.biUnion markedWheelArcs)
    let SR := S\(KS∪N.biUnion markedWheelSpokePairs);
    N.biUnion markedWheelPhysicalResources=M.biUnion markedWheelPhysicalResources ∧
    (∀ Y∈N,∀ Z∈N,Y≠Z→Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Z)) ∧
    N.biUnion markedWheelArcs⊆Finset.univ\KA ∧ N.biUnion markedWheelSpokePairs⊆S\KS ∧
    MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) AR SR m ∧
    markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π AR SR=
      markedFiniteResources (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) π (Finset.univ\M.biUnion markedWheelArcs)
        (S'\M.biUnion markedWheelSpokePairs) := by
  intro E K S KA KS DR DS σ' H' E' K' S' hdiv M hM N AR SR
  obtain ⟨hRes,hN,hNA,hNS,_,_⟩ := marked_canonical_deleted_packing P π d m σ H KA KS M hM
  have hbase : MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) (Finset.univ\KA) (S\KS) m := by
    apply (markedFiniteBalance_eq_zero_iff _ _ _ _ _ _ _ _).mp
    intro z i
    rw [←(marked_canonical_deleted_balance_values P π d m σ H KA KS Finset.univ Finset.univ z i).1]
    exact (markedFiniteBalance_eq_zero_iff _ _ _ _ _ _ _ _).mpr hdiv z i
  have hdivR := marked_packing_remainder_divisible hH (Finset.univ\KA) (S\KS) hbase N hN hNA hNS
  have hA : (Finset.univ\KA)\N.biUnion markedWheelArcs=AR := by
    ext a
    simp only [AR,Finset.mem_sdiff,Finset.mem_union]
    tauto
  have hS : (S\KS)\N.biUnion markedWheelSpokePairs=SR := by
    ext s
    simp only [SR,Finset.mem_sdiff,Finset.mem_union]
    tauto
  rw [hA,hS] at hdivR
  refine ⟨hRes,hN,hNA,hNS,hdivR,?_⟩
  have hp := markedSampleArc_physical_injective P π (3*d) (fun e=>σ (Sum.inl e))
  have hp' := markedSampleArc_physical_injective P π (3*d) (fun e=>σ' (Sum.inl e))
  rw [←hA,←hS,markedFiniteResources_sdiff _ _ _ _ π hp,
    markedPackingResources_eq_finite,markedFiniteResources_sdiff _ _ _ _ π hp',markedPackingResources_eq_finite,hRes]
  have hc := marked_deleted_sample_resources P π d σ H KA KS
  rw [←markedFiniteResources_sdiff _ _ _ _ π hp] at hc
  rw [hc]

end Oberwolfach
