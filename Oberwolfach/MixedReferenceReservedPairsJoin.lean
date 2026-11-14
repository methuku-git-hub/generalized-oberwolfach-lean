module

public import Oberwolfach.MixedRetainedReservedPairs

@[expose] public section
/-! Intersect an arbitrary marked reference event with the reserved-spoke
codegrees on the same expanded sample and the same start retention. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U]

theorem mixed_reference_and_retained_reserved_pairs
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d) (a j:Bool) (α:ℝ)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Bool→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Bool→ℝ) (hs:∀w j,0≤s w j)
    (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let μret:=μ.sigma (mixedClassActualRetention true π d a);
    ∀ (E:(Σω:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e),
      mixedClassRetentionSpace true π d a ω)→Prop) (ε ζ:ℝ),
      1-ε≤μret.probability E→
      1-ζ≤μret.probability (fun z=>rawIntervalReservedMatchingEvent π d (fun e=>z.1 (Sum.inr e)) j α)→
      1-ε-ζ≤μret.probability (fun z=>E z ∧
        let σ:=fun e=>z.1 (Sum.inr e)
        let J:StartRetentionOutcome (rawStartHubSet π d σ a) (startRetentionMinimum (rawStartHubSet π d σ a)):=z.2
        let Outer:=fun w=>Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d σ a
          (startRetentionMinimum (rawStartHubSet π d σ a)) J a j false v w);
        ∀x y:V,x≠y→2*α*Fintype.card V≤
          ((((Finset.univ:Finset U).filter (fun w=>x∈Outer w))∩
            ((Finset.univ:Finset U).filter (fun w=>y∈Outer w))).card:ℝ)):=by
  intro μ μret E ε ζ hE hR
  have hh:=finiteLaw_good_intersection μret E
    (fun z=>rawIntervalReservedMatchingEvent π d (fun e=>z.1 (Sum.inr e)) j α) ζ hR
  have hp:1-ε-ζ≤μret.probability (fun z=>E z ∧
    rawIntervalReservedMatchingEvent π d (fun e=>z.1 (Sum.inr e)) j α):=by linarith
  apply hp.trans
  apply finiteLaw_probability_mono
  intro z hz
  exact ⟨hz.1,mixed_retained_reserved_pairs π d a j α z hz.2⟩

def mixedRetainedReservationReady (π:Equiv.Perm V) (d:ℕ) (a j:Bool) (α:ℝ)
    (z:Σω:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e),
      mixedClassRetentionSpace true π d a ω):Prop:=
    let σ:=fun e=>z.1 (Sum.inr e)
    let J:StartRetentionOutcome (rawStartHubSet π d σ a) (startRetentionMinimum (rawStartHubSet π d σ a)):=z.2
    let Outer:=fun w=>Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d σ a
      (startRetentionMinimum (rawStartHubSet π d σ a)) J a j false v w);
    (∀x y:V,x≠y→2*α*Fintype.card V≤
      ((((Finset.univ:Finset U).filter (fun w=>x∈Outer w))∩
        ((Finset.univ:Finset U).filter (fun w=>y∈Outer w))).card:ℝ)) ∧
    ∀ (C:Finset (Finset V⊕(V×U))) (Hold:Bool→V→U→Prop) (Inner:Finset U)
      (K:SimpleGraph V) (Old:U→Finset V) (Bad:V→Finset U),
      (Inner.card:ℝ)+2*C.card≤α*Fintype.card V→
      (∀w,Disjoint (Old w) (Outer w))→
      let S:=fun e=>commonOuterPairIndices Outer e\Inner;
      let A:=actualReservedOrdinarySpokeLabels C Hold;
      let L:=reservedSpokeMatchingList S A;
      (∀e∈K.edgeFinset,α*Fintype.card V≤((L e).card:ℝ)) ∧
      (∀e∈K.edgeFinset,Disjoint (L e) Inner) ∧
      (∀w e v,e∈K.edgeFinset→v∈e.toFinset→v∈Old w→w∈L e→w∈Bad v) ∧
      (∀e∈K.edgeFinset,∀v∈e.toFinset,∀w∈L e,v∉A w)

theorem mixed_reserved_event_gives_retained_ready
    (π:Equiv.Perm V) (d:ℕ) (a j:Bool) (α:ℝ)
    (z:Σω:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e),
      mixedClassRetentionSpace true π d a ω)
    (h:rawIntervalReservedMatchingEvent π d (fun e=>z.1 (Sum.inr e)) j α):
    mixedRetainedReservationReady π d a j α z:=by
  exact ⟨mixed_retained_reserved_pairs π d a j α z h,mixed_retained_reserved_lists π d a j α z h⟩

theorem mixed_reference_and_retained_reservation
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d) (a j:Bool) (α:ℝ)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Bool→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Bool→ℝ) (hs:∀w j,0≤s w j)
    (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let μret:=μ.sigma (mixedClassActualRetention true π d a);
    ∀ (E:(Σω:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e),
      mixedClassRetentionSpace true π d a ω)→Prop) (ε ζ:ℝ),
      1-ε≤μret.probability E→
      1-ζ≤μret.probability (fun z=>rawIntervalReservedMatchingEvent π d (fun e=>z.1 (Sum.inr e)) j α)→
      1-ε-ζ≤μret.probability (fun z=>E z ∧ mixedRetainedReservationReady π d a j α z):=by
  intro μ μret E ε ζ hE hR
  have hh:=finiteLaw_good_intersection μret E
    (fun z=>rawIntervalReservedMatchingEvent π d (fun e=>z.1 (Sum.inr e)) j α) ζ hR
  have hp:1-ε-ζ≤μret.probability (fun z=>E z ∧
    rawIntervalReservedMatchingEvent π d (fun e=>z.1 (Sum.inr e)) j α):=by linarith
  apply hp.trans
  apply finiteLaw_probability_mono
  intro z hz
  exact ⟨hz.1,mixed_reserved_event_gives_retained_ready π d a j α z hz.2⟩

end Oberwolfach
