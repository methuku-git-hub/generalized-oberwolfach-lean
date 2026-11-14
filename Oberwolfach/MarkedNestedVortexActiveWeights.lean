module

public import Oberwolfach.MarkedVortexActiveDomainEquivalences
public import Oberwolfach.VortexSuccessorWeightFamilies
public import Oberwolfach.SuccessorWeightsRelabel

@[expose] public section
/-! Transport the existing physical-difference-set weights to the nested
vertex and hub types of marked cover-down, preserving the actual target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_nested_vortex_active_successor_weights
    (k c:ℕ) (hlen:c+1=(k+2)*2) (α τ:ℝ) (hα:0<α) (hτ:0<τ)
    (hmargin:successorCycleRatio k+α/4≤1/2+α/2):
    ∃ βmax:ℝ,0<βmax ∧ ∀ b:ℕ,∃ N:ℕ,1≤N ∧
    ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m),
    G.IsRegularOfDegree D→0<Fintype.card V→
    (1/2+α)*Fintype.card V≤(D:ℝ)→0 < initialIndexDensity U D→
    0≤β→β≤βmax→0<ε→ε≤1/4→(N:ℝ)≤3*ε*m/8→
    ∀ L:ℕ,L≤Q.length→
    let W:=fun i=>markedVortexVertexType Q i
    let Z:=fun i=>markedVortexHubType Q i
    let T:=fun i=>markedVortexInnerVertices Q i
    let S:=fun i=>markedVortexInnerHubs Q i
    let A:∀ i,Finset (W i):=fun i=>Finset.univ\T i
    let B:∀ i,Finset (Z i):=fun i=>Finset.univ\S i
    let P:=fun i=>G.comap (markedVortexVertexEmbedding Q i)
    let Dactive:=fun i=>2*((B i).card:ℝ)/initialIndexDensity U D;
    ∀ πA:∀ i,Equiv.Perm (A i:Set (W i)),
    ∃ weight:∀ i,(Fin (c+1)→(A i:Set (W i)))→ℝ,
      ∀ i≤L,SuccessorSequenceWeightConditions ((P i).induce (A i:Set (W i)))
        (πA i) b (Dactive i) τ (successorWeightLower k (α/4)) (successorWeightUpper k (α/4)) (weight i):=by
  obtain ⟨βmax,hβmax,hbase⟩:=vortex_difference_successor_weight_families k c hlen α τ hα hτ hmargin
  refine ⟨βmax,hβmax,?_⟩
  intro b
  obtain ⟨N,hN,hbase⟩:=hbase b
  refine ⟨N,hN,?_⟩
  intro V U _ _ _ _ G D m β ε Q hreg hn hD hρ hb hbmax he he1 hsize L hL W Z T S A B P Dactive πA
  let R:=fun i=>Q.extendedVertices i\Q.extendedVertices (i+1)
  let K:=fun i=>Q.extendedIndices i\Q.extendedIndices (i+1)
  let f:=fun i=>markedVortexActiveVertexEquiv Q i
  let g:=fun i=>markedVortexActiveHubEquiv Q i
  let πR:∀ i,Equiv.Perm (R i):=fun i=>(f i).symm.trans ((πA i).trans (f i))
  obtain ⟨w,hw⟩:=hbase V U G D m β ε Q hreg hn hD hρ hb hbmax he he1 hsize 1 (by omega) (by omega) πR
  refine ⟨fun i z=>w i ((f i) ∘ z),?_⟩
  intro i hi
  have hcomm:∀ x,f i (πA i x)=πR i (f i x):=by
    intro x
    change f i (πA i x)=f i (πA i ((f i).symm (f i x)))
    rw [Equiv.symm_apply_apply]
  have hK:(K i).card=(B i).card:=by
    have hh:=Fintype.card_congr (g i)
    change Fintype.card ↥(B i)=Fintype.card ↥(K i) at hh
    simpa only [Fintype.card_coe] using hh.symm
  have hwt:=successor_sequence_weights_relabel (f i) (G.comap (Subtype.val:R i→V))
    (πR i) (πA i) hcomm b (2*(K i).card/initialIndexDensity U D) τ
    (successorWeightLower k (α/4)) (successorWeightUpper k (α/4)) (w i) (hw i (hi.trans hL))
  rw [hK] at hwt
  exact hwt
end Oberwolfach
