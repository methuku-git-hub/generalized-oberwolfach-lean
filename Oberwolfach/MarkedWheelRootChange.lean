module

public import Oberwolfach.MarkedWheelIntegerResources

@[expose] public section

/-! A root change affects precisely the arcs incident with the changed
positions. The equality is proved for actual physical resources, including
the successor image at the marked head. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {m:ℕ} {π:Equiv.Perm V} {b:ℕ}
    {H₀ Hₖ:V→U→Prop}

 theorem marked_wheel_rim_position_unchanged
    (W W':MarkedWheel tail head ktail khead m π b H₀ Hₖ) (i:Fin (m+1))
    (h₁:W.1.val i=W'.1.val i)
    (h₂:W.1.val (finRotate (m+1) i)=W'.1.val (finRotate (m+1) i)):
    markedWheelPositionResource W (Sum.inl i)=markedWheelPositionResource W' (Sum.inl i):=by
  rw [markedWheelPositionResource_rim_formula,markedWheelPositionResource_rim_formula,h₁]
  by_cases hi:i=Fin.last m
  · subst i
    rw [finRotate_last] at h₂
    simp only [ite_true,h₂]
  · simp only [hi,ite_false,h₂]

 theorem integer_difference_sum_restrict {I:Type} [Fintype I] [DecidableEq I]
    (f g:I→ℤ) (S:Finset I) (h:∀ i,i∉S→f i=g i):
    (∑ i,(f i-g i))=∑ i∈S,(f i-g i):=by
  apply Eq.symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i hi hiS
  rw [h i hiS,sub_self]

 theorem marked_wheel_root_change_identity
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (W W':MarkedWheel tail head ktail khead m π b H₀ Hₖ)
    (S:Finset (Fin (m+1))) (hag:∀ i,i∉S→W.1.val i=W'.1.val i)
    (e:Finset V⊕(V×U)):
    (if e∈markedWheelPhysicalResources W then (1:ℤ) else 0)-
      (if e∈markedWheelPhysicalResources W' then 1 else 0)=
      (∑ i∈Finset.univ.filter (fun i=>i∈S∨finRotate (m+1) i∈S),
        physicalIntDelta (markedWheelPositionResource W (Sum.inl i))
          (markedWheelPositionResource W' (Sum.inl i)) e)+
      ∑ i,physicalIntDelta (markedWheelPositionResource W (Sum.inr i))
        (markedWheelPositionResource W' (Sum.inr i)) e:=by
  rw [markedWheelPhysicalResources_integer_difference hp]
  congr 1
  apply Eq.symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i hi hiS
  have hout:i∉S∧finRotate (m+1) i∉S:=by
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,not_or] using hiS
  rw [marked_wheel_rim_position_unchanged W W' i (hag i hout.1) (hag _ hout.2)]
  simp [physicalIntDelta]

 theorem marked_wheel_same_hub_root_change_identity
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (W W':MarkedWheel tail head ktail khead m π b H₀ Hₖ)
    (S:Finset (Fin (m+1))) (hag:∀ i,i∉S→W.1.val i=W'.1.val i)
    (hU:W.2.val=W'.2.val) (e:Finset V⊕(V×U)):
    (if e∈markedWheelPhysicalResources W then (1:ℤ) else 0)-
      (if e∈markedWheelPhysicalResources W' then 1 else 0)=
      (∑ i∈Finset.univ.filter (fun i=>i∈S∨finRotate (m+1) i∈S),
        physicalIntDelta (markedWheelPositionResource W (Sum.inl i))
          (markedWheelPositionResource W' (Sum.inl i)) e)+
      ∑ i∈S,physicalIntDelta (markedWheelPositionResource W (Sum.inr i))
        (markedWheelPositionResource W' (Sum.inr i)) e:=by
  rw [marked_wheel_root_change_identity hp W W' S hag]
  congr 1
  apply Eq.symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i hi hiS
  simp only [markedWheelPositionResource,hag i hiS,hU,physicalIntDelta,sub_self]

end Oberwolfach
