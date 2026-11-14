module

public import Oberwolfach.MixedCommonOutcomeMatchingInputs

@[expose] public section
/-! Add the matching inputs to any event witnessed by the same mixed outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U]

def MixedOutcomeMatchingInputs (π:Equiv.Perm V) (d:ℕ)
    (z:Σω:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e),
      mixedClassRetentionSpace true π d false ω):Prop:=
    let sample:RawIntervalFamilyOutcome V U Bool Bool:=fun e=>rawExpandedMarkedCollapse (Sum.inr e) (z.1 (Sum.inr e))
    let t:=startRetentionMinimum (rawStartHubSet π d sample false)
    let J:StartRetentionOutcome (rawStartHubSet π d sample false) t:=z.2
    let k:=fun w (_:retainedMarkedIndex π d sample false t J w)=>d
    let a:=fun w (j:retainedMarkedIndex π d sample false t J w)=>j.val
    let Y:=fun w=>markedIntervalRootSet π (k w) (a w)
    let B:=fun w=>Finset.univ.image (fun j=>(π^d) (a w j))
    (∀w j,0<k w j) ∧ (∀w j,k w j≤d) ∧
    (∀w j,Function.Injective (fun i:Fin (k w j+1)=>(π^i.val) (a w j))) ∧
    (∀w j l,j≠l→Disjoint (permutationWindow π 0 (k w j) (a w j))
      (permutationWindow π 0 (k w l) (a w l))) ∧
    (∀v,(Finset.univ.filter (fun w=>v∈Y w)).card=d*t) ∧
    (∀w,Disjoint (Y w) (B w)) ∧ (∀w,(Y w).image π⊆Y w ∪ B w) ∧
    (∀w v,v∈Y w↔retainedRawFamilyState π d sample false t J (v,w)=some (Sum.inl false))

theorem mixed_common_event_with_matching_inputs
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (P:(Σω:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e),
      mixedClassRetentionSpace true π d false ω)→Prop)
    (hP:∃z,P z):∃z,P z ∧ MixedOutcomeMatchingInputs π d z:=by
  obtain ⟨z,hz⟩:=hP
  refine ⟨z,hz,?_⟩
  unfold MixedOutcomeMatchingInputs
  exact mixed_common_outcome_retained_matching_inputs π d hd hnoshort z
end Oberwolfach
