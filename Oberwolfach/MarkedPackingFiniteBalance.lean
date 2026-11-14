module

public import Oberwolfach.MarkedWheelFiniteBalance
public import Oberwolfach.MarkedFiniteDivisibilityOperations

@[expose] public section

/-! Removing a physically edge-disjoint marked wheel packing preserves all
four integer divisibility identities on the actual typed remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T:Type} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq T]
    {tail head:E→V} {ktail khead:T→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

omit [Fintype V] [Fintype U] in
theorem markedWheel_arc_resource (W:MarkedWheel tail head ktail khead m π b H₀ HK)
    (a:E⊕T) (ha:a∈markedWheelArcs W):
    Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈markedWheelPhysicalResources W:=by
  obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp ha
  apply (markedWheelPhysicalResources_rim W _).mpr
  exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

omit [Fintype V] [Fintype U] in
theorem markedWheel_spoke_resource (W:MarkedWheel tail head ktail khead m π b H₀ HK)
    (s:V×U):s∈markedWheelSpokePairs W↔Sum.inr s∈markedWheelPhysicalResources W:=by
  rcases s with ⟨v,u⟩
  simp only [markedWheelSpokePairs,Finset.mem_image,Finset.mem_univ,true_and,
    markedWheelPhysicalResources_spoke,Prod.mk.injEq]
  aesop

theorem marked_packing_finite_divisible
    (hH:∀ v u,¬(H₀ v u∧HK v u))
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (hM:∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z)):
    MarkedRemainderDivisible tail head ktail khead HK
      (M.biUnion markedWheelArcs) (M.biUnion markedWheelSpokePairs) m:=by
  induction M using Finset.induction_on with
  | empty=>constructor <;> intro x <;> simp
  | @insert W M hW ih=>
    rw [Finset.biUnion_insert,Finset.biUnion_insert]
    have hdis (Z) (hZ:Z∈M):Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z):=
      hM W (Finset.mem_insert_self _ _) Z (Finset.mem_insert_of_mem hZ) (fun he=>hW (he ▸ hZ))
    apply marked_finite_divisible_union
    · apply Finset.disjoint_left.mpr
      intro a ha hb
      obtain ⟨Z,hZ,hb⟩:=Finset.mem_biUnion.mp hb
      exact Finset.disjoint_left.mp (hdis Z hZ) (markedWheel_arc_resource W a ha) (markedWheel_arc_resource Z a hb)
    · apply Finset.disjoint_left.mpr
      intro s hs ht
      obtain ⟨Z,hZ,ht⟩:=Finset.mem_biUnion.mp ht
      exact Finset.disjoint_left.mp (hdis Z hZ) ((markedWheel_spoke_resource W s).mp hs) ((markedWheel_spoke_resource Z s).mp ht)
    · exact markedWheel_finite_divisible hH W
    · exact ih (fun Z hZ Y hY hne=>hM Z (Finset.mem_insert_of_mem hZ) Y (Finset.mem_insert_of_mem hY) hne)

theorem marked_packing_remainder_divisible
    (hH:∀ v u,¬(H₀ v u∧HK v u))
    (A:Finset (E⊕T)) (S:Finset (V×U))
    (hAS:MarkedRemainderDivisible tail head ktail khead HK A S m)
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (hM:∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))
    (hA:M.biUnion markedWheelArcs⊆A) (hS:M.biUnion markedWheelSpokePairs⊆S):
    MarkedRemainderDivisible tail head ktail khead HK
      (A\M.biUnion markedWheelArcs) (S\M.biUnion markedWheelSpokePairs) m:=
  marked_finite_divisible_sdiff A _ S _ hA hS hAS (marked_packing_finite_divisible hH M hM)

end Oberwolfach
