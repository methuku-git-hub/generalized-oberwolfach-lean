module

public import Oberwolfach.MarkedCorrectionOutsideResources
public import Oberwolfach.MarkedPackingFiniteBalance

@[expose] public section
/-! A wheel packing selected from the outside resources can be removed while
retaining divisibility of the outside-plus-correction remainder. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E T:Type} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq T]
    {tail head:E→V} {ktail khead:T→V} {HK H₀:V→U→Prop} {m b:ℕ} {π:Equiv.Perm V}

theorem marked_correction_outside_after_matching_divisible
    (A B C:Finset (E⊕T)) (S R T':Finset (V×U))
    (hA:B⊆A) (hS:R⊆S) (hAC:Disjoint A C) (hST:Disjoint S T')
    (hwhole:MarkedRemainderDivisible tail head ktail khead HK (A∪C) (S∪T') m)
    (hrest:MarkedRemainderDivisible tail head ktail khead HK (A\B) (S\R) m)
    (hH:∀v u,¬(H₀ v u∧HK v u))
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (hM:∀W∈M,∀Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))
    (hArc:M.biUnion markedWheelArcs⊆C) (hSpoke:M.biUnion markedWheelSpokePairs⊆T'):
    MarkedRemainderDivisible tail head ktail khead HK
      ((B∪C)\M.biUnion markedWheelArcs) ((R∪T')\M.biUnion markedWheelSpokePairs) m := by
  have h:=marked_correction_with_outside_divisible A B C S R T' hA hS hAC hST hwhole hrest
  exact marked_packing_remainder_divisible hH (B∪C) (R∪T') h M hM
    (hArc.trans Finset.subset_union_right) (hSpoke.trans Finset.subset_union_right)
end Oberwolfach
