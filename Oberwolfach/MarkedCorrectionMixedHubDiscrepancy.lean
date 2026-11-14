module

public import Oberwolfach.MarkedCorrectionOutsideResources
public import Oberwolfach.MarkedMixedHubDiscrepancy

@[expose] public section
/-! Signed hub accounting for the correction plus the outside resources after
a mixed matching, without imposing a common length on its components. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T I:Type} [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq T] [DecidableEq I]
    {tail head:E→V} {ktail khead:T→V} {HK:V→U→Prop}

theorem marked_correction_outside_mixed_hub_discrepancy
    (m:ℕ) (A B C:Finset (E⊕T)) (S R T':Finset (V×U))
    (hA:B⊆A) (hS:R⊆S) (hAC:Disjoint A C) (hST:Disjoint S T')
    (hwhole:MarkedRemainderDivisible tail head ktail khead HK (A∪C) (S∪T') m)
    (hrest:MarkedRemainderDivisible tail head ktail khead HK (A\B) (S\R) m)
    (M:Finset I) (spoke:I→Finset (V×U))
    (hdis:∀i∈M,∀j∈M,i≠j→Disjoint (spoke i) (spoke j))
    (hSpoke:M.biUnion spoke⊆T') (u:U):
    markedFiniteHubDiscrepancy HK m ((R∪T')\M.biUnion spoke) u =
      -(∑i∈M,markedFiniteHubDiscrepancy HK m (spoke i) u) := by
  have hbase:=marked_correction_with_outside_divisible A B C S R T' hA hS hAC hST hwhole hrest
  have hsub:M.biUnion spoke⊆R∪T':=hSpoke.trans Finset.subset_union_right
  have h:=marked_finite_balanced_remainder_hub_discrepancy tail head ktail khead HK m
    (B∪C) (R∪T') (M.biUnion spoke) hsub hbase u
  rw [marked_finite_hub_discrepancy_biUnion HK m M spoke hdis u] at h
  exact h
end Oberwolfach
