module

public import Oberwolfach.MarkedCorrectionDivisibilityAccounting

@[expose] public section
/-! The removed correction can be kept together with resources outside the
sample. Balance of their union follows from balance of the whole resource set
and of the corrected remainder; no balance of the correction alone is used. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E T:Type} [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq T]
    {tail head:E→V} {ktail khead:T→V} {HK:V→U→Prop} {m:ℕ}

theorem marked_correction_with_outside_divisible
    (A B C:Finset (E⊕T)) (S R T':Finset (V×U))
    (hA:B⊆A) (hS:R⊆S) (hAC:Disjoint A C) (hST:Disjoint S T')
    (hwhole:MarkedRemainderDivisible tail head ktail khead HK (A∪C) (S∪T') m)
    (hrest:MarkedRemainderDivisible tail head ktail khead HK (A\B) (S\R) m):
    MarkedRemainderDivisible tail head ktail khead HK (B∪C) (R∪T') m := by
  have hsubA:A\B⊆A∪C:=(Finset.sdiff_subset).trans (Finset.subset_union_left)
  have hsubS:S\R⊆S∪T':=(Finset.sdiff_subset).trans (Finset.subset_union_left)
  have h:=marked_finite_divisible_sdiff (A∪C) (A\B) (S∪T') (S\R) hsubA hsubS hwhole hrest
  have heA:(A∪C)\(A\B)=B∪C:=by
    ext x
    have hs:x∈B→x∈A:=fun hx=>hA hx
    have hd:¬(x∈A ∧ x∈C):=by
      intro hh
      exact (Finset.disjoint_left.mp hAC) hh.1 hh.2
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  have heS:(S∪T')\(S\R)=R∪T':=by
    ext x
    have hs:x∈R→x∈S:=fun hx=>hS hx
    have hd:¬(x∈S ∧ x∈T'):=by
      intro hh
      exact (Finset.disjoint_left.mp hST) hh.1 hh.2
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  simpa only [heA,heS] using h
end Oberwolfach
