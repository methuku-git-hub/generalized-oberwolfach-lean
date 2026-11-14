module

public import Oberwolfach.MixedMarkedReservedMatchingEvent
public import Oberwolfach.RetainedOrdinarySpokesMonotone

@[expose] public section
/-! Connect the Extra event on the actual expanded sample to the ordinary
spokes after the same start-retention outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U]

theorem mixed_retained_reserved_pairs
    (π:Equiv.Perm V) (d:ℕ) (a j:Bool) (α:ℝ)
    (z:Σω:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e),
       mixedClassRetentionSpace true π d a ω)
    (h:rawIntervalReservedMatchingEvent π d (fun e=>z.1 (Sum.inr e)) j α):
    let σ:=fun e=>z.1 (Sum.inr e)
    let J:StartRetentionOutcome (rawStartHubSet π d σ a) (startRetentionMinimum (rawStartHubSet π d σ a)):=z.2
    let Outer:=fun u=>Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d σ a
       (startRetentionMinimum (rawStartHubSet π d σ a)) J a j false v u);
    ∀x y:V,x≠y→2*α*Fintype.card V≤
      ((((Finset.univ:Finset U).filter (fun u=>x∈Outer u))∩
        ((Finset.univ:Finset U).filter (fun u=>y∈Outer u))).card:ℝ):=by
  intro σ J Outer
  exact raw_reserved_matching_event_retained_pairs π d σ a _ J a j α h

theorem mixed_retained_reserved_lists
    (π:Equiv.Perm V) (d:ℕ) (a j:Bool) (α:ℝ)
    (z:Σω:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e),
       mixedClassRetentionSpace true π d a ω)
    (h:rawIntervalReservedMatchingEvent π d (fun e=>z.1 (Sum.inr e)) j α):
    let σ:=fun e=>z.1 (Sum.inr e)
    let J:StartRetentionOutcome (rawStartHubSet π d σ a) (startRetentionMinimum (rawStartHubSet π d σ a)):=z.2
    let Outer:=fun u=>Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d σ a
       (startRetentionMinimum (rawStartHubSet π d σ a)) J a j false v u);
    ∀ (C:Finset (Finset V⊕(V×U))) (Hold:Bool→V→U→Prop) (Inner:Finset U)
      (K:SimpleGraph V) (Old:U→Finset V) (Bad:V→Finset U),
      (Inner.card:ℝ)+2*C.card≤α*Fintype.card V→
      (∀u,Disjoint (Old u) (Outer u))→
      let S:=fun e=>commonOuterPairIndices Outer e\Inner;
      let A:=actualReservedOrdinarySpokeLabels C Hold;
      let L:=reservedSpokeMatchingList S A;
      (∀e∈K.edgeFinset,α*Fintype.card V≤((L e).card:ℝ)) ∧
      (∀e∈K.edgeFinset,Disjoint (L e) Inner) ∧
      (∀u e v,e∈K.edgeFinset→v∈e.toFinset→v∈Old u→u∈L e→u∈Bad v) ∧
      (∀e∈K.edgeFinset,∀v∈e.toFinset,∀u∈L e,v∉A u):=by
  intro σ J Outer
  exact raw_reserved_matching_event_retained_lists π d σ a _ J a j α h

end Oberwolfach
