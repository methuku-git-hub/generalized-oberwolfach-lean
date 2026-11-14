module

public import Oberwolfach.MarkedInnerDeletionBudgets

@[expose] public section
/-! A packing that avoids the inner star adds no physical change inside
the protected pair. Existing prescribed changes are accounted for exactly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {m b:ℕ} {H₀ HK:V→U→Prop}

theorem marked_protected_pair_avoided_by_packing
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK)) (I:Finset V) (J:Finset U)
    (hstar:(M.biUnion markedWheelPhysicalResources).filter (markedStarResource I J)=∅)
    (ER:SimpleGraph V) (ES:SimpleGraph (V⊕U))
    (hER:∀ x∈I,∀ y∈I,¬ER.Adj x y)
    (hES:∀ x∈I,∀ u∈J,¬ES.Adj (Sum.inl x) (Sum.inr u)):
    let FR:=ER⊔markedPackingRimGraph M
    let FS:=ES⊔markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)
    (∀ x∈I,∀ y∈I,¬FR.Adj x y) ∧
    (∀ x∈I,∀ u∈J,¬FS.Adj (Sum.inl x) (Sum.inr u)) :=by
  intro FR FS
  have hr:=marked_inner_deletion_has_only_prescribed_cost M I J hstar ER ES
  constructor
  · intro x hx y hy hxy
    have hh:y∈FR.neighborFinset x∩I:=Finset.mem_inter.mpr ⟨(SimpleGraph.mem_neighborFinset _ _ _).mpr hxy,hy⟩
    rw [hr.1 x] at hh
    exact hER x hx y hy ((SimpleGraph.mem_neighborFinset _ _ _).mp (Finset.mem_inter.mp hh).1)
  · intro x hx u hu hxu
    have hh:Sum.inr u∈FS.neighborFinset (Sum.inl x)∩J.image Sum.inr:=
      Finset.mem_inter.mpr ⟨(SimpleGraph.mem_neighborFinset _ _ _).mpr hxu,Finset.mem_image.mpr ⟨u,hu,rfl⟩⟩
    rw [hr.2.2.1 (Sum.inl x)] at hh
    exact hES x hx u hu ((SimpleGraph.mem_neighborFinset _ _ _).mp (Finset.mem_inter.mp hh).1)
end Oberwolfach
