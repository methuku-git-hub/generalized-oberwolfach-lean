module

public import Oberwolfach.MarkedFullSpokeWeightedSum

@[expose] public section
/-! A rim condition depends on the cycle, not on its hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V}

theorem marked_full_rim_weighted_sum
    (w:MarkedCycleTuple tail head ktail khead m π b→ℝ) (a:U→ℝ) (e:E⊕K):
    (∑ W:MarkedWheel tail head ktail khead m π b (fun (_:V) (_:U)=>True) (fun _ _=>True),
      if Sum.inl e∈typedMarkedOccurrenceResources W then w W.1*a W.2.val else 0)=
    (∑ C:MarkedCycleTuple tail head ktail khead m π b,
      if CanonicalMarkedArcMem C e then w C else 0)*(∑ u,a u) := by
  rw [←Equiv.sum_comp markedFullWheelEquiv,Fintype.sum_prod_type,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro C _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  change (if Sum.inl e∈typedMarkedOccurrenceResources (markedFullWheel C u) then w C*a u else 0)=_
  have he:Sum.inl e∈typedMarkedOccurrenceResources (markedFullWheel C u) ↔ CanonicalMarkedArcMem C e :=
    typedMarkedOccurrenceResources_rim (markedFullWheel C u) e
  split_ifs <;> simp_all
end Oberwolfach
