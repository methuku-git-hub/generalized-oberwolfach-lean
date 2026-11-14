module

public import Oberwolfach.MarkedSampleArcs
public import Oberwolfach.RawMarkedResourceCoordinates
public import Oberwolfach.MarkedHostExtensionCounts

@[expose] public section

/-! Exact interfaces between the sampled arc identifiers, the raw rim
predicate and the auxiliary/physical endpoints used by the absorber. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V]

theorem marked_sample_host_arc_present
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (j:Bool) (x y:V):
    markedArcPresent
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2) j x y↔
      rawMarkedPairRims P π d σ (if j then Sum.inr (x,y) else Sum.inl (x,y)):=by
  cases j <;> simp only [markedArcPresent,rawMarkedPairRims,ite_false,ite_true,Bool.false_eq_true,Sum.elim_inl,Sum.elim_inr]
  all_goals
    constructor
    · rintro ⟨⟨⟨v,w⟩,h⟩,rfl,rfl⟩
      exact h
    · intro h
      exact ⟨⟨(x,y),h⟩,rfl,rfl⟩

theorem marked_sample_host_arc_separated
    (P:SimpleGraph V) (π:Equiv.Perm V) (b:ℕ) (σ:Sym2 V→Option (Bool×Bool)) (j:Bool)
    (a:MarkedSampleArc P π b σ j):¬PermutationClose π b a.val.1 a.val.2:=
  ((markedPhysicalRim_eq_one_iff P π b σ j a.val.1 a.val.2).mp a.property).1

end Oberwolfach
