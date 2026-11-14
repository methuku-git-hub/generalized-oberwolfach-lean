module

public import Oberwolfach.MarkedFixedVortexSuccessorWeights
public import Oberwolfach.MarkedFixedVortexEventInputs
public import Oberwolfach.MarkedFixedVortexReferenceDegreeInputs
public import Oberwolfach.MarkedFixedVortexScaleInputs

@[expose] public section
/-! Assemble fixed-vortex successor weights and the deterministic geometry,
size, degree and density-centre inputs for the reference event. These inputs
are chosen before any sampling densities or outcomes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_fixed_vortex_deterministic_reference_inputs
    (k c:ℕ) (hlen:c+1=(k+2)*2) (α τ ρ₀:ℝ) (hα:0<α) (hτ:0<τ) (hr:0<ρ₀)
    (hmargin:successorCycleRatio k+α/4≤1/2+α/2):
    ∃ βmax:ℝ,0<βmax ∧ ∀ b:ℕ,∃ N:ℕ,1≤N ∧ ∀ β ε:ℝ,
    0≤β→β≤βmax→0<ε→ε<1/4→∀ M:ℕ,∃ m₀:ℕ,1≤m₀ ∧
    ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ) (Q:Vortex U G D β ε m),
    G.IsRegularOfDegree D→0<Fintype.card V→(1/2+α)*Fintype.card V≤(D:ℝ)→
    ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D ≤ 1→m₀≤m→
    ∀ (π:Equiv.Perm V) (hpres:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (L:ℕ),L<Q.length→
    let W:=markedVortexVertexType Q
    let Z:=markedVortexHubType Q
    let f:=markedVortexVertexEmbedding Q
    let ρ:=markedVortexPermutation Q π hpres
    let I:=markedVortexInnerVertices Q
    let J:=markedVortexInnerHubs Q
    let dens:=initialIndexDensity U D
    let Dbal:=fun i=>2*((J i).card:ℝ)/dens
    let Dload:=fun i=>2*(Fintype.card (Z i):ℝ)/dens
    ∃ weight:∀ i,(Fin (c+1)→W i)→ℝ,
    ∀ s:ℝ,∀ r:ℕ,0<r→
    let p:=dens*s/2
    let kden:=p/(r:ℝ)
    ∀ i≤L,
      SuccessorSequenceWeightConditions (G.comap (f i)) (ρ i) b (Dload i) τ
        (successorWeightLower k (α/4)) (successorWeightUpper k (α/4)) (weight i) ∧
      (M:ℝ)≤(1-ε)*((I i).card:ℝ) ∧ (M:ℝ)≤(1-ε)*((J i).card:ℝ) ∧
      (I i).card≤Fintype.card (W i) ∧ (J i).card≤Fintype.card (W i) ∧
      Fintype.card (Z i)≤Fintype.card (W i) ∧
      (Fintype.card (W (i+1)):ℝ)≤ε*Fintype.card (W i) ∧
      (∀ x:W i,(1/2+α/2)*((I i).card:ℝ)≤(((G.comap (f i)).neighborFinset x∩I i).card:ℝ)) ∧
      (∀ x:W i,|(((G.comap (f i)).neighborFinset x∩I i).card:ℝ)-Dbal i|≤β*Fintype.card (W i)) ∧
      (∀ x:W i,(1/2+α/2)*(Fintype.card (W i):ℝ)≤((G.comap (f i)).degree x:ℝ)) ∧
      (∀ x:W i,|((G.comap (f i)).degree x:ℝ)-Dload i|≤β*Fintype.card (W i)) ∧
      ((Fintype.card (W i):ℝ)/2≤Dload i) ∧ (Dload i≤2*Fintype.card (W i)) ∧
      p*Dbal i=s*(J i).card ∧ kden*Dbal i=(s/r)*(J i).card ∧
      (Fintype.card (Z i):ℝ)*(s/r)=Dload i*kden ∧
      (Fintype.card (Z i):ℝ)*(s/r)*r=Dload i*p:=by
  obtain ⟨βorig,hβorig,hweights⟩:=marked_fixed_vortex_successor_weight_families k c hlen α τ hα hτ hmargin
  let βmax:=min βorig (min (α/8) (1/4:ℝ))
  have hβmax:0<βmax:=by dsimp [βmax];positivity
  refine ⟨βmax,hβmax,?_⟩
  intro b
  obtain ⟨N,hN,hweights⟩:=hweights b
  refine ⟨N,hN,?_⟩
  intro β ε hb hβ he he1 M
  have hβorig':β≤βorig:=hβ.trans (min_le_left _ _)
  have hbα:β≤α/8:=hβ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hb1:β≤1/4:=hβ.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨mSize,hmSize,hsize⟩:=marked_fixed_vortex_event_size_inputs β ε ρ₀ hb hb1 he he1 hr M
  obtain ⟨mWeight,hmWeight⟩:=exists_nat_gt (2*(N:ℝ)/ε)
  refine ⟨max mSize (max mWeight 1),by omega,?_⟩
  intro V U _ _ _ _ G D m Q hreg hn hD hrlo hrhi hm π hpres L hL W Z f ρ I J dens Dbal Dload
  have hmpos:0<m:=by omega
  have hρ:0 < initialIndexDensity U D:=hr.trans_le hrlo
  have hweightSize:(N:ℝ)≤ε*m/2:=by
    have hmreal:(mWeight:ℝ)≤m:=by exact_mod_cast (show mWeight≤m by omega)
    have hh:=hmWeight.trans_le hmreal
    have hh':2*(N:ℝ)<(m:ℝ)*ε:=(div_lt_iff₀ he).1 hh
    nlinarith
  obtain ⟨weight,hw⟩:=hweights V U G D m β ε Q hreg hn hD hρ hb hβorig' he hweightSize π hpres L hL
  refine ⟨weight,?_⟩
  intro s r hrpos p kden i hi
  have hhalf:(Fintype.card V:ℝ)/2≤D:=by
    have hnonneg:(0:ℝ)≤Fintype.card V:=Nat.cast_nonneg _
    nlinarith [mul_nonneg hα.le hnonneg]
  have hfields:=marked_vortex_reference_degree_inputs Q hreg hn hD hα hρ hb hbα hb1 he hmpos i (by omega) s r hrpos
  have hscale:=marked_vortex_reference_scale_inputs Q hreg hn hhalf hr hrlo hrhi hb hb1 he hmpos i (by omega)
  have hs:=hsize V U G D m hreg hn hhalf hrlo hrhi (by omega) Q i (by omega)
  exact ⟨hw i hi,hs.2.1,hs.2.2.1,hscale.1,hscale.2.1,hscale.2.2.1,hscale.2.2.2,hfields⟩
end Oberwolfach
