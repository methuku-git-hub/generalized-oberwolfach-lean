module

public import Oberwolfach.FiniteWeightedPartitionBadExplicit
public import Oberwolfach.OrdinaryNonrootWheelBadIff

@[expose] public section
/-! Partition a parent rim load into wheels supported on the nonroot
domains and wheels touching an excluded root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_nonroot_wheel_rim_partition (Q F:SimpleGraph V) (H:V→U→Prop) (r:ℕ)
    (T:Finset V) (W:Finset U) [Fintype (OrdinaryWheel Q F H r)]
    [Fintype {C:OrdinaryWheel Q F H r // (ordinaryWheelRim C).support⊆(↑(Finset.univ\T):Set V) ∧
      ordinaryWheelHub C∈Finset.univ\W}] (w:OrdinaryWheel Q F H r→ℝ) (x y:V):
    (∑ C:OrdinaryWheel Q F H r,if (ordinaryWheelRim C).Adj x y then w C else 0)=
      (∑ C:{C:OrdinaryWheel Q F H r // (ordinaryWheelRim C).support⊆(↑(Finset.univ\T):Set V) ∧
          ordinaryWheelHub C∈Finset.univ\W},if (ordinaryWheelRim C.val).Adj x y then w C.val else 0)+
      ∑C,if (ordinaryWheelRim C).Adj x y ∧
        (ordinaryWheelHub C∈W ∨ ∃z∈T,z∈(ordinaryWheelRim C).support) then w C else 0:=by
  have hp:=finite_weighted_partition_with_bad_explicit
    (fun C:OrdinaryWheel Q F H r=>(ordinaryWheelRim C).Adj x y)
    (fun C=>(ordinaryWheelRim C).support⊆(↑(Finset.univ\T):Set V) ∧ ordinaryWheelHub C∈Finset.univ\W)
    (fun C=>ordinaryWheelHub C∈W ∨ ∃z∈T,z∈(ordinaryWheelRim C).support) w
    (ordinary_nonroot_wheel_bad_iff Q F H r T W)
  convert hp using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
