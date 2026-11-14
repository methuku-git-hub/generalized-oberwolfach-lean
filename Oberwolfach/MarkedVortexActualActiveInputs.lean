module

public import Oberwolfach.MarkedVortexActiveDegreeFields

@[expose] public section
/-! The actual active vortex sets, original permutation, degree estimates
and fixed successor weights are chosen together before sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_actual_active_inputs
    (k c:ℕ) (hlen:c+1=(k+2)*2) (α τ:ℝ) (hα:0<α) (hτ:0<τ)
    (hmargin:successorCycleRatio k+α/4≤1/2+α/2):
    ∃ βmax:ℝ,0<βmax ∧ ∀ b:ℕ,∃ N:ℕ,1≤N ∧
    ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m),
    G.IsRegularOfDegree D→0<Fintype.card V→
    (1/2+α)*Fintype.card V≤(D:ℝ)→0 < initialIndexDensity U D→
    0≤β→β≤βmax→0<ε→ε≤1/4→(N:ℝ)≤3*ε*m/8→
    ∀ (π:Equiv.Perm V) (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (L:ℕ),L≤Q.length→
    let W:=fun i=>markedVortexVertexType Q i
    let Z:=fun i=>markedVortexHubType Q i
    let A:∀ i,Finset (W i):=fun i=>Finset.univ\markedVortexInnerVertices Q i
    let B:∀ i,Finset (Z i):=fun i=>Finset.univ\markedVortexInnerHubs Q i
    let P:=fun i=>G.comap (markedVortexVertexEmbedding Q i)
    let Dactive:=fun i=>2*((B i).card:ℝ)/initialIndexDensity U D;
    ∃ weight:∀ i,(Fin (c+1)→(A i:Set (W i)))→ℝ,
      ∀ i≤L,
      SuccessorSequenceWeightConditions ((P i).induce (A i:Set (W i)))
        (markedVortexActivePermutation Q π hπ i) b (Dactive i) τ
        (successorWeightLower k (α/4)) (successorWeightUpper k (α/4)) (weight i) ∧
      (∀ x:(A i:Set (W i)),
        ((A i).card:ℝ)/2≤Dactive i ∧ Dactive i≤2*(A i).card ∧
        (1/2+α/2)*(A i).card≤((G.comap (markedVortexActiveVertexEmbedding Q i)).degree x:ℝ) ∧
        |((G.comap (markedVortexActiveVertexEmbedding Q i)).degree x:ℝ)-Dactive i|≤(5/3)*β*(A i).card) ∧
      (∀ x:(A i:Set (W i)),markedVortexActiveVertexEmbedding Q i (markedVortexActivePermutation Q π hπ i x)=
        π (markedVortexActiveVertexEmbedding Q i x)):=by
  obtain ⟨βbase,hβbase,hbase⟩:=marked_nested_vortex_active_successor_weights k c hlen α τ hα hτ hmargin
  let βmax:=min βbase (min (3*α/40) (3/20))
  have hβmax:0<βmax:=by dsimp [βmax];positivity
  refine ⟨βmax,hβmax,?_⟩
  intro b
  obtain ⟨N,hN,hbase⟩:=hbase b
  refine ⟨N,hN,?_⟩
  intro V U _ _ _ _ G D m β ε Q hreg hn hD hρ hb hbmax he he1 hsize π hπ L hL W Z A B P Dactive
  have hbbase:β≤βbase:=hbmax.trans (min_le_left _ _)
  have hbα:β≤3*α/40:=hbmax.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hb1:β≤3/20:=hbmax.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨weight,hweight⟩:=hbase V U G D m β ε Q hreg hn hD hρ hb hbbase he he1 hsize L hL
    (fun i=>markedVortexActivePermutation Q π hπ i)
  refine ⟨weight,?_⟩
  intro i hi
  refine ⟨hweight i hi,?_,?_⟩
  · intro x
    exact marked_vortex_active_degree_fields Q hreg hn hD hα hρ hb hbα hb1 he.le he1 i x
  · intro x
    exact marked_vortex_active_permutation_embedding Q π hπ i x
end Oberwolfach
