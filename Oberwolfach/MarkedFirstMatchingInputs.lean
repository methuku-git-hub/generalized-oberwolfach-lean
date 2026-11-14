module

public import Oberwolfach.MixedRetainedReservedPairs
public import Oberwolfach.MarkedInitialReservedLoss
public import Oberwolfach.MarkedOccupiedAvoidsOuter

@[expose] public section
/-! Construct the first-cover matching lists from the retained sample, the
first vortex index set, and the actual bounded reserved absorber. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_first_matching_inputs
    (αRes:ℝ) (hαRes:0<αRes) (B:ℕ):
    ∃ N:ℕ,∀ (V U:Type) [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m),
    N≤Fintype.card V→G.IsRegularOfDegree D→0<Fintype.card V→
    ∀ (αHost ρ₀:ℝ),0<αHost→0<ρ₀→
    (1/2+αHost)*Fintype.card V≤(D:ℝ)→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→
    0≤ε→ε≤αRes/2→
    ∀ (π:Equiv.Perm V) (d:ℕ),1≤d→∀ (a g j j':Bool),g≠a→j'≠j→
    ∀ (z:Σω:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e),
      mixedClassRetentionSpace true π d a ω),
    rawIntervalReservedMatchingEvent π d (fun e=>z.1 (Sum.inr e)) j αRes→
    let σ:=fun e=>z.1 (Sum.inr e)
    let J:StartRetentionOutcome (rawStartHubSet π d σ a) (startRetentionMinimum (rawStartHubSet π d σ a)):=z.2
    let Hold:=retainedRawMarkedSpokes π d σ a (startRetentionMinimum (rawStartHubSet π d σ a)) J a j
    let Outer:=fun w=>Finset.univ.filter (fun v=>Hold false v w)
    let Inner:=Q.extendedIndices 1;
    ∀ (C:Finset (Finset V⊕(V×U))) (K:SimpleGraph V) (Old:U→Finset V) (Bad:V→Finset U),
    C.card≤B→
    (∀w v,v∈Old w→
      rawMarkedSpokes π d σ g j' false v w ∨
      rawMarkedSpokes π d σ g j true v w ∨
      (∃x,π x=v ∧ rawMarkedSpokes π d σ g j true x w) ∨
      Hold true v w ∨ (∃x,π x=v ∧ Hold true x w))→
    let S:=fun e=>commonOuterPairIndices Outer e\Inner
    let A:=actualReservedOrdinarySpokeLabels C Hold
    let L:=reservedSpokeMatchingList S A;
    (∀x y:V,x≠y→2*αRes*Fintype.card V≤
      ((((Finset.univ:Finset U).filter (fun w=>x∈Outer w))∩
        ((Finset.univ:Finset U).filter (fun w=>y∈Outer w))).card:ℝ)) ∧
    ((Inner.card:ℝ)+2*C.card≤αRes*Fintype.card V) ∧
    (∀w,Disjoint (Old w) (Outer w)) ∧
    (∀e∈K.edgeFinset,αRes*Fintype.card V≤((L e).card:ℝ)) ∧
    (∀e∈K.edgeFinset,Disjoint (L e) Inner) ∧
    (∀w e v,e∈K.edgeFinset→v∈e.toFinset→v∈Old w→w∈L e→w∈Bad v) ∧
    (∀e∈K.edgeFinset,∀v∈e.toFinset,∀w∈L e,v∉A w):=by
  obtain ⟨N,hN⟩:=marked_initial_reserved_loss αRes hαRes B
  refine ⟨N,?_⟩
  intro V U _ _ _ _ _ G D m β ε Q hn hreg hV αHost ρ₀ hαHost hρ₀ hD hρlo hρhi he heRes π d hd a g j j' hg hj z hE σ J Hold Outer Inner C K Old Bad hC hOld S A L
  have hLoss:=hN V U G D m β ε Q hn hreg hV αHost ρ₀ hαHost hρ₀ hD hρlo hρhi he heRes C hC
  have hOldOuter:∀w,Disjoint (Old w) (Outer w):=
    marked_occupied_with_raw_approximate_intervals_avoid_outer π d hd σ a g hg _ J j j' hj Old hOld
  refine ⟨mixed_retained_reserved_pairs π d a j αRes z hE,hLoss,hOldOuter,?_⟩
  exact mixed_retained_reserved_lists π d a j αRes z hE C Hold Inner K Old Bad hLoss hOldOuter
end Oberwolfach
