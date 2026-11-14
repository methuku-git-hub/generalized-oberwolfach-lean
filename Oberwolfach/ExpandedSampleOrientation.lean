module

public import Oberwolfach.MarkedExpandedApproximateProjection
public import Oberwolfach.MarkedSampleArcs
public import Oberwolfach.RawMixedPhysicalArcHost
public import Oberwolfach.RawSelectedPhysicalNeighbourTests
public import Oberwolfach.RandomOrientation

@[expose] public section
/-! Both exposed physical layers use the same sampled direction bit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem expanded_collapse_direction
    (z:Fin 6×Bool) (mark bit:Bool):
    markedExpandedPhysicalCollapse z=some (mark,bit) → z.2=bit:=by
  intro h
  unfold markedExpandedPhysicalCollapse at h
  split_ifs at h <;> simp_all

theorem expanded_approximate_collapse_direction
    (z:Fin 6×Bool) (mark bit:Bool):
    markedExpandedApproximateCollapse z=some (mark,bit) → z.2=bit:=by
  intro h
  unfold markedExpandedApproximateCollapse at h
  split_ifs at h <;> simp_all

theorem expanded_selected_rim_uses_sampled_orientation
    {V:Type} [LinearOrder V] (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:Sym2 V→Fin 6×Bool) (mark:Bool) (x y:V):
    markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω e)) mark x y=1 →
      sampledOrientation P (fun e=>(ω e).2) x (if mark then π y else y)=1:=by
  intro h
  have hh:=(markedPhysicalRim_eq_one_iff P π (3*d) _ mark x y).mp h
  have hb:=expanded_collapse_direction (ω s(x,if mark then π y else y)) mark (orientationBit x (if mark then π y else y)) hh.2.2
  simp [sampledOrientation,hh.2.1,hb]

theorem expanded_approximate_rim_uses_sampled_orientation
    {V:Type} [LinearOrder V] (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:Sym2 V→Fin 6×Bool) (mark:Bool) (x y:V):
    markedPhysicalRim P π (3*d) (fun e=>markedExpandedApproximateCollapse (ω e)) mark x y=1 →
      sampledOrientation P (fun e=>(ω e).2) x (if mark then π y else y)=1:=by
  intro h
  have hh:=(markedPhysicalRim_eq_one_iff P π (3*d) _ mark x y).mp h
  have hb:=expanded_approximate_collapse_direction (ω s(x,if mark then π y else y)) mark (orientationBit x (if mark then π y else y)) hh.2.2
  simp [sampledOrientation,hh.2.1,hb]

theorem expanded_selected_relation_uses_sampled_orientation
    {V:Type} [Fintype V] [LinearOrder V] (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:Sym2 V→Fin 6×Bool) (x y:V):
    rawSelectedPhysicalRelation P π d ω x y → sampledOrientation P (fun e=>(ω e).2) x y=1:=by
  intro h
  simpa using expanded_selected_rim_uses_sampled_orientation P π d ω false x y h

theorem expanded_approximate_arc_uses_sampled_orientation
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) (x y:V):
    rawMixedPhysicalArc P π d (fun e=>rawExpandedApproximateCollapse e (σ e)) x y →
      sampledOrientation P (fun e=>(σ (Sum.inl e)).2) x y=1:=by
  intro h
  rcases h with h|h
  · exact expanded_approximate_rim_uses_sampled_orientation P π d (fun e=>σ (Sum.inl e)) false x y h
  · have hh:=expanded_approximate_rim_uses_sampled_orientation P π d (fun e=>σ (Sum.inl e)) true x (π.symm y) h
    simpa only [Bool.true_eq_false,ite_true,Equiv.apply_symm_apply] using hh
end Oberwolfach
