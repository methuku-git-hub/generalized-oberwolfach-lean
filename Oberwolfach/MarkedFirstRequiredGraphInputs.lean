module

public import Oberwolfach.MarkedFirstMatchingInputs
public import Oberwolfach.LongRequiredVortexRowMargins

@[expose] public section
/-! Joint first-stage matching and required-graph margins on the same retained
sample, using the fixed inner vortex set and original physical row count. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_first_required_graph_inputs
    (α lam:ℝ) (hα:0<α) (hlam:0<lam) (B:ℕ) (d:ℕ) (hd:2≤d):
    ∃ N:ℕ,∀ (V U:Type) [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U]
      (G P₀ Sel Used:SimpleGraph V) (Dv m:ℕ) (β ε:ℝ) (Q:Vortex U G Dv β ε m),
    N≤Fintype.card V→G.IsRegularOfDegree Dv→0<Fintype.card V→
    ∀ (αHost ρ₀:ℝ),0<αHost→0<ρ₀→
    (1/2+αHost)*Fintype.card V≤(Dv:ℝ)→ρ₀≤ initialIndexDensity U Dv→initialIndexDensity U Dv≤1→
    ∀ (π:Equiv.Perm V) (D M:V→V→Prop) (a g j j':Bool),g≠a→j'≠j→
    ∀ (z:Σω:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e),
      mixedClassRetentionSpace true π d a ω),
    rawIntervalReservedMatchingEvent π d (fun e=>z.1 (Sum.inr e)) j α→
    let σ:=fun e=>z.1 (Sum.inr e)
    let J:StartRetentionOutcome (rawStartHubSet π d σ a) (startRetentionMinimum (rawStartHubSet π d σ a)):=z.2
    let Hold:=retainedRawMarkedSpokes π d σ a (startRetentionMinimum (rawStartHubSet π d σ a)) J a j
    let Outer:=fun w=>Finset.univ.filter (fun v=>Hold false v w)
    let Inner:=Q.extendedIndices 1
    let I:=Q.extendedVertices 1
    let K:=longRequiredPhysicalGraph G P₀ Sel π d I D M;
    P₀≤longPhysicalStateGraph G z.1 {0,1,2,3,4}\Used→
    (∀x∈I,∀y∈I,(longSelectedPhysicalGraph G π d z.1).Adj x y→Sel.Adj x y)→
    ∀ (θ C₀ u:ℝ),0≤θ→θ≤1/100→0≤ε→1≤C₀→ε≤α/(1000*C₀)→
    lam≤α/128→0≤u→u≤2*θ→
    (∀v∈I,|(((G.neighborFinset v∩I).filter (fun w=>(z.1 (Sum.inl s(v,w))).1=4)).card:ℝ)-
      u*(G.neighborFinset v∩I).card|<(Fintype.card V:ℝ)^(3/4:ℝ))→
    (∀v∈I,((longPhysicalStateGraph G z.1 {2,3}\Used).degree v:ℝ)≤lam*Fintype.card V)→
    ∀ (C:Finset (Finset V⊕(V×U))) (Old:U→Finset V),C.card≤B→
    (∀w v,v∈Old w→
      rawMarkedSpokes π d σ g j' false v w ∨
      rawMarkedSpokes π d σ g j true v w ∨
      (∃x,π x=v ∧ rawMarkedSpokes π d σ g j true x w) ∨
      Hold true v w ∨ (∃x,π x=v ∧ Hold true x w))→
    let S:=fun e=>commonOuterPairIndices Outer e\Inner
    let A:=actualReservedOrdinarySpokeLabels C Hold
    let L:=reservedSpokeMatchingList S A;
    (∀x y:V,x≠y→2*α*Fintype.card V≤
      ((((Finset.univ:Finset U).filter (fun w=>x∈Outer w))∩
        ((Finset.univ:Finset U).filter (fun w=>y∈Outer w))).card:ℝ)) ∧
    ((Inner.card:ℝ)+2*C.card≤α*Fintype.card V) ∧
    (∀w,Disjoint (Old w) (Outer w)) ∧
    (∀v,(K.degree v:ℝ)≤(α/16)*Fintype.card V) ∧
    (K.edgeFinset.card:ℝ)≤(θ*ε^2+lam*ε)*(Fintype.card V:ℝ)^2+24*d*Fintype.card V ∧
    (∀e∈K.edgeFinset,α*Fintype.card V≤((L e).card:ℝ)) ∧
    (∀e∈K.edgeFinset,Disjoint (L e) Inner) ∧
    (∀e∈K.edgeFinset,∀v∈e.toFinset,∀w∈L e,v∉A w):=by
  obtain ⟨N₁,hN₁⟩:=marked_first_matching_inputs α hα B
  obtain ⟨N₂,hN₂⟩:=long_required_vortex_row_margins α lam hα hlam d (by omega)
  refine ⟨max N₁ N₂,?_⟩
  intro V U _ _ _ _ _ G P₀ Sel Used Dv m β ε Q hn hreg hV αHost ρ₀ hαHost hρ₀ hD hρlo hρhi π D M a g j j' hg hj z hEvent
    σ J Hold Outer Inner I K hP₀ hSelected θ C₀ u hθ hθhi he hC hehi hlamhi hu huhi hrow hB C Old hCcard hOld S A L
  have hehalf:ε≤α/2:=by
    have hh:α/(1000*C₀)≤α/1000:=div_le_div_of_nonneg_left hα.le (by positivity) (by nlinarith)
    linarith
  have hmatch:=hN₁ V U G Dv m β ε Q (le_trans (le_max_left _ _) hn) hreg hV
    αHost ρ₀ hαHost hρ₀ hD hρlo hρhi he hehalf π d (by omega) a g j j' hg hj z hEvent C K Old (fun _=>∅) hCcard hOld
  have hgraph:=hN₂ V U Bool Bool G P₀ Sel Used Dv m β ε Q (le_trans (le_max_right _ _) hn)
    π D M z.1 hP₀ hSelected θ C₀ u hθ hθhi he hC hehi hlamhi hu huhi hrow hB
  exact ⟨hmatch.1,hmatch.2.1,hmatch.2.2.1,hgraph.1,hgraph.2,
    hmatch.2.2.2.1,hmatch.2.2.2.2.1,hmatch.2.2.2.2.2.2⟩
end Oberwolfach
