module

public import Oberwolfach.MarkedFixedVortexSuccessorWeights
public import Oberwolfach.SuccessorWeightsPreserveParent

@[expose] public section
/-! Successor weights on the actual fixed vortex subtypes. The entire family
is selected before the sampling densities and outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_fixed_vortex_successor_weights_with_fixed_parent
    (k c:ℕ) (hlen:c+1=(k+2)*2) (α τ:ℝ) (hα:0<α) (hτ:0<τ)
    (hmargin:successorCycleRatio k+α/4≤1/2+α/2):
    ∃ βmax:ℝ,0<βmax ∧ ∀ b:ℕ,∃ N:ℕ,1≤N ∧
    ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m),
    G.IsRegularOfDegree D→0<Fintype.card V→
    (1/2+α)*Fintype.card V≤(D:ℝ)→0 < initialIndexDensity U D→
    0≤β→β≤βmax→0<ε→(N:ℝ)≤ε*m/2→
    ∀ (π:Equiv.Perm V) (hpres:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (L:ℕ),L<Q.length→
    let W:=markedVortexVertexType Q
    let Z:=markedVortexHubType Q
    let f:=markedVortexVertexEmbedding Q
    let ρ:=markedVortexPermutation Q π hpres
    let Dload:=fun i=>2*(Fintype.card (Z i):ℝ)/initialIndexDensity U D
    ∀ parent:(Fin (c+1)→W 0)→ℝ,
      SuccessorSequenceWeightConditions (G.comap (f 0)) (ρ 0) b (Dload 0) τ
        (successorWeightLower k (α/4)) (successorWeightUpper k (α/4)) parent→
    ∃ weight:∀ i,(Fin (c+1)→W i)→ℝ,weight 0=parent ∧
      ∀ i≤L,SuccessorSequenceWeightConditions (G.comap (f i)) (ρ i) b (Dload i) τ
        (successorWeightLower k (α/4)) (successorWeightUpper k (α/4)) (weight i):=by
  obtain ⟨βmax,hβmax,hbase⟩:=marked_fixed_vortex_successor_weight_families k c hlen α τ hα hτ hmargin
  refine ⟨βmax,hβmax,?_⟩
  intro b
  obtain ⟨N,hN,hbase⟩:=hbase b
  refine ⟨N,hN,?_⟩
  intro V U _ _ _ _ G D m β ε Q hreg hn hD hρ hb hβmax he hsize π hpres L hL W Z f ρ Dload parent hparent
  obtain ⟨weight,hw⟩:=hbase V U G D m β ε Q hreg hn hD hρ hb hβmax he hsize π hpres L hL
  obtain ⟨updated,hzero,_,hupdated⟩:=successor_weight_family_preserve_parent W c b
    (fun i=>G.comap (f i)) ρ Dload τ (successorWeightLower k (α/4)) (successorWeightUpper k (α/4))
    L weight hw parent hparent
  exact ⟨updated,hzero,hupdated⟩
end Oberwolfach
