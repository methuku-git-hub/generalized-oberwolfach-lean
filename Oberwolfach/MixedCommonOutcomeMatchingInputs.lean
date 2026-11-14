module

public import Oberwolfach.RetainedMarkedMatchingInputs
public import Oberwolfach.MixedClassActualRetention

@[expose] public section
/-! The common mixed outcome itself supplies the retained matching inputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem mixed_common_outcome_retained_matching_inputs
    {V U:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (z:Σω:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e),
      mixedClassRetentionSpace true π d false ω):
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
    (∀w v,v∈Y w↔retainedRawFamilyState π d sample false t J (v,w)=some (Sum.inl false)):=by
  intro sample t J k a Y B
  exact retained_marked_matching_inputs π d hd hnoshort sample false t J
end Oberwolfach
