module

public import Oberwolfach.MarkedCorrectionOutsideAfterMatching
public import Oberwolfach.MarkedFiniteResourceOperations

@[expose] public section
/-! Translate physical disjointness from the reference sample into the typed
outside-resource hypotheses used in the correction accounting. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype T]
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq T]
    {tail head:E→V} {ktail khead:T→V} {HK H₀:V→U→Prop} {m b:ℕ} {π:Equiv.Perm V}

theorem marked_correction_outside_after_physically_disjoint_matching
    (A B C:Finset (E⊕T)) (S R T':Finset (V×U))
    (hA:B⊆A) (hS:R⊆S) (hAC:Disjoint A C) (hST:Disjoint S T')
    (hwhole:MarkedRemainderDivisible tail head ktail khead HK (A∪C) (S∪T') m)
    (hrest:MarkedRemainderDivisible tail head ktail khead HK (A\B) (S\R) m)
    (hH:∀v u,¬(H₀ v u∧HK v u))
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (hM:∀W∈M,∀Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))
    (hArcAll:M.biUnion markedWheelArcs⊆A∪C)
    (hSpokeAll:M.biUnion markedWheelSpokePairs⊆S∪T')
    (hPhysical:Disjoint (markedFiniteResources tail head ktail khead π A S)
      (M.biUnion markedWheelPhysicalResources)):
    MarkedRemainderDivisible tail head ktail khead HK
      ((B∪C)\M.biUnion markedWheelArcs) ((R∪T')\M.biUnion markedWheelSpokePairs) m := by
  have hPhysical':Disjoint (markedFiniteResources tail head ktail khead π A S)
      (markedFiniteResources tail head ktail khead π (M.biUnion markedWheelArcs)
        (M.biUnion markedWheelSpokePairs)) := by
    rw [markedPackingResources_eq_finite]
    exact hPhysical
  have hArcDis:Disjoint A (M.biUnion markedWheelArcs) := by
    apply Finset.disjoint_left.mpr
    intro a ha hm
    have hleft:Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈
        markedFiniteResources tail head ktail khead π A S := by
      change _∈A.image _ ∪ S.image Sum.inr
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
    have hright:Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈
        markedFiniteResources tail head ktail khead π (M.biUnion markedWheelArcs)
          (M.biUnion markedWheelSpokePairs) := by
      change _∈(M.biUnion markedWheelArcs).image _ ∪ (M.biUnion markedWheelSpokePairs).image Sum.inr
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,hm,rfl⟩)
    exact (Finset.disjoint_left.mp hPhysical') hleft hright
  have hSpokeDis:Disjoint S (M.biUnion markedWheelSpokePairs) := by
    apply Finset.disjoint_left.mpr
    intro z hz hm
    have hleft:Sum.inr z∈markedFiniteResources tail head ktail khead π A S := by
      change _∈A.image _ ∪ S.image Sum.inr
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z,hz,rfl⟩)
    have hright:Sum.inr z∈markedFiniteResources tail head ktail khead π (M.biUnion markedWheelArcs)
        (M.biUnion markedWheelSpokePairs) := by
      change _∈(M.biUnion markedWheelArcs).image _ ∪ (M.biUnion markedWheelSpokePairs).image Sum.inr
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z,hm,rfl⟩)
    exact (Finset.disjoint_left.mp hPhysical') hleft hright
  have hArc:M.biUnion markedWheelArcs⊆C := by
    intro a ha
    rcases Finset.mem_union.mp (hArcAll ha) with h | h
    · exact False.elim ((Finset.disjoint_left.mp hArcDis) h ha)
    · exact h
  have hSpoke:M.biUnion markedWheelSpokePairs⊆T' := by
    intro z hz
    rcases Finset.mem_union.mp (hSpokeAll hz) with h | h
    · exact False.elim ((Finset.disjoint_left.mp hSpokeDis) h hz)
    · exact h
  exact marked_correction_outside_after_matching_divisible A B C S R T' hA hS hAC hST hwhole hrest hH M hM hArc hSpoke
end Oberwolfach
