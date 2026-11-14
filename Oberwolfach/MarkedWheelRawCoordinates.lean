module

public import Oberwolfach.MarkedWheelIntegerResources
public import Oberwolfach.MarkedCycleRotation

@[expose] public section

/-! Physical resource sums in the original directed cyclic order, before
the marked head is rotated to position zero. -/
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

 def markedRawRimResource (π:Equiv.Perm V) (z:Fin (m+1)→V) (k i:Fin (m+1)):
    Finset V⊕(V×U):=
  Sum.inl (if i=k then {z i,π (z (finRotate (m+1) i))} else {z i,z (finRotate (m+1) i)})

 theorem marked_wheel_raw_rim_position (W:MarkedWheel tail head ktail khead m π b H₀ Hₖ)
    (z:Fin (m+1)→V) (k:Fin (m+1))
    (hW:∀ i,W.1.val i=z (canonicalMarkedRotation k i)) (i:Fin (m+1)):
    markedWheelPositionResource W (Sum.inl ((canonicalMarkedRotation k).symm i))=
      markedRawRimResource π z k i:=by
  let ρ:=canonicalMarkedRotation k
  have hi:ρ.symm i=Fin.last m↔i=k:=by
    constructor
    · intro he
      have hh:=congrArg ρ he
      simpa only [Equiv.apply_symm_apply,ρ,canonicalMarkedRotation_last] using hh
    · intro he
      apply ρ.injective
      simpa only [Equiv.apply_symm_apply,ρ,canonicalMarkedRotation_last] using he
  have hz:W.1.val (ρ.symm i)=z i:=by rw [hW];simp only [ρ,Equiv.apply_symm_apply]
  have hs:W.1.val (finRotate (m+1) (ρ.symm i))=z (finRotate (m+1) i):=by
    rw [hW,canonicalMarkedRotation_rotate]
    simp only [ρ,Equiv.apply_symm_apply]
  rw [markedWheelPositionResource_rim_formula]
  change Sum.inl (if ρ.symm i=Fin.last m then {W.1.val (ρ.symm i),π (W.1.val 0)}
    else {W.1.val (ρ.symm i),W.1.val (finRotate (m+1) (ρ.symm i))})=_
  rw [hz]
  by_cases hik:i=k
  · rw [if_pos (hi.mpr hik)]
    simp only [markedRawRimResource,hik,ite_true,hW,canonicalMarkedRotation_zero]
  · simp only [hi, hik,ite_false,markedRawRimResource,hs]

 theorem marked_wheel_raw_integer_positions
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (W:MarkedWheel tail head ktail khead m π b H₀ Hₖ)
    (z:Fin (m+1)→V) (k:Fin (m+1))
    (hW:∀ i,W.1.val i=z (canonicalMarkedRotation k i)) (e:Finset V⊕(V×U)):
    (if e∈markedWheelPhysicalResources W then (1:ℤ) else 0)=
      (∑ i,if e=markedRawRimResource π z k i then 1 else 0)+
      ∑ i,if e=Sum.inr (z i,W.2.val) then 1 else 0:=by
  rw [markedWheelPhysicalResources_integer_positions hp]
  have hr:=Equiv.sum_comp (canonicalMarkedRotation k).symm
    (fun i=>if e=markedWheelPositionResource W (Sum.inl i) then (1:ℤ) else 0)
  have hs:=Equiv.sum_comp (canonicalMarkedRotation k).symm
    (fun i=>if e=markedWheelPositionResource W (Sum.inr i) then (1:ℤ) else 0)
  rw [← hr,← hs]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [marked_wheel_raw_rim_position W z k hW]
  · apply Finset.sum_congr rfl
    intro i hi
    simp only [markedWheelPositionResource,hW,Equiv.apply_symm_apply]

 theorem marked_wheel_raw_integer_difference
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (W W':MarkedWheel tail head ktail khead m π b H₀ Hₖ)
    (z z':Fin (m+1)→V) (k:Fin (m+1))
    (hW:∀ i,W.1.val i=z (canonicalMarkedRotation k i))
    (hW':∀ i,W'.1.val i=z' (canonicalMarkedRotation k i)) (e:Finset V⊕(V×U)):
    (if e∈markedWheelPhysicalResources W then (1:ℤ) else 0)-
      (if e∈markedWheelPhysicalResources W' then 1 else 0)=
      (∑ i,physicalIntDelta (markedRawRimResource π z k i) (markedRawRimResource π z' k i) e)+
      ∑ i,physicalIntDelta (Sum.inr (z i,W.2.val)) (Sum.inr (z' i,W'.2.val)) e:=by
  rw [marked_wheel_raw_integer_positions hp W z k hW,
    marked_wheel_raw_integer_positions hp W' z' k hW']
  simp only [physicalIntDelta,Finset.sum_sub_distrib]
  ring

end Oberwolfach
