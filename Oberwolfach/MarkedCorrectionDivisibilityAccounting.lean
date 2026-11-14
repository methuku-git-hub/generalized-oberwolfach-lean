module

public import Oberwolfach.MarkedFiniteDivisibilityOperations
public import Oberwolfach.MarkedPackingFiniteBalance

@[expose] public section
/-! The correction and the corrected remainder partition the original typed
resources.  If the remainder is divisible, the correction is divisible exactly
when the original resources are divisible. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E T:Type} [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq T]
    {tail head:E→V} {ktail khead:T→V} {HK:V→U→Prop} {m:ℕ}

theorem marked_correction_divisible_iff_original
    (A B:Finset (E⊕T)) (S R:Finset (V×U))
    (hA:B⊆A) (hS:R⊆S)
    (hrest:MarkedRemainderDivisible tail head ktail khead HK (A\B) (S\R) m):
    MarkedRemainderDivisible tail head ktail khead HK B R m ↔
      MarkedRemainderDivisible tail head ktail khead HK A S m := by
  constructor
  · intro hcor
    have hArc:Disjoint B (A\B):=by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      exact (Finset.mem_sdiff.mp hy).2 hx
    have hSpoke:Disjoint R (S\R):=by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      exact (Finset.mem_sdiff.mp hy).2 hx
    have h:=marked_finite_divisible_union B (A\B) R (S\R) hArc hSpoke hcor hrest
    simpa only [Finset.union_sdiff_of_subset hA,Finset.union_sdiff_of_subset hS] using h
  · intro hfull
    have h:=marked_finite_divisible_sdiff A (A\B) S (S\R)
      (Finset.sdiff_subset) (Finset.sdiff_subset) hfull hrest
    have heA:A\(A\B)=B:=by
      ext x
      simp only [Finset.mem_sdiff]
      have hh:x∈B→x∈A:=fun hx=>hA hx
      tauto
    have heS:S\(S\R)=R:=by
      ext x
      simp only [Finset.mem_sdiff]
      have hh:x∈R→x∈S:=fun hx=>hS hx
      tauto
    simpa only [heA,heS] using h
/-- A wheel packing of the correction can account for the original resources
only if the original typed sample already satisfies the balance identities. -/
theorem marked_correction_wheel_cover_forces_original_divisible
    [Fintype V] [Fintype U] {π:Equiv.Perm V} {b:ℕ} {H₀:V→U→Prop}
    (hH:∀v u,¬(H₀ v u∧HK v u))
    (A B:Finset (E⊕T)) (S R:Finset (V×U))
    (hA:B⊆A) (hS:R⊆S)
    (hrest:MarkedRemainderDivisible tail head ktail khead HK (A\B) (S\R) m)
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (hM:∀W∈M,∀Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))
    (hArc:M.biUnion markedWheelArcs=B) (hSpoke:M.biUnion markedWheelSpokePairs=R):
    MarkedRemainderDivisible tail head ktail khead HK A S m := by
  apply (marked_correction_divisible_iff_original A B S R hA hS hrest).mp
  simpa only [hArc,hSpoke] using marked_packing_finite_divisible hH M hM
end Oberwolfach
