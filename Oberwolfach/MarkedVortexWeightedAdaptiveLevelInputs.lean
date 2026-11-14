module

public import Oberwolfach.MarkedVortexAdaptiveLevelInputs
public import Oberwolfach.MarkedFixedVortexSuccessorWeights

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem marked_fixed_vortex_weighted_adaptive_level_inputs
    (k₀ r d:ℕ) (hlen:r+4+1=(k₀+2)*2)
    (ε ρ₀ α τ:ℝ) (he:0<ε) (he1:ε<1/4) (hρ₀:0<ρ₀) (hα:0<α) (hτ:0<τ)
    (hmargin:successorCycleRatio k₀+α/4≤1/2+α/2):
    ∃K:ℝ,1≤K ∧ ∃βmax:ℝ,0<βmax ∧ ∀ (β γ δPbal δP:ℝ),
    0≤β → β≤1/4 → β≤α/8 → β≤βmax → 0≤γ → γ≤α/2 → β≤δPbal → β≤δP →
    ∀M:ℕ,∃m₀:ℕ,1≤m₀ ∧
    ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ),G.IsRegularOfDegree D→0<Fintype.card V→
      (1/2+α)*Fintype.card V≤(D:ℝ)→ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D≤1→
      m₀≤m→∀(Q:Vortex U G D β ε m) (π:Equiv.Perm V)
      (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (L:ℕ),L<Q.length→∀ s₀:ℝ,
    let W:=markedVortexVertexType Q
    let Z:=markedVortexHubType Q
    let f:=markedVortexVertexEmbedding Q
    let ρi:=markedVortexPermutation Q π hpres
    let I:=markedVortexInnerVertices Q
    let J:=markedVortexInnerHubs Q
    let dens:=initialIndexDensity U D
    let p:=dens*s₀/2
    let k:=dens*(s₀/((r+4:ℕ):ℝ))/2
    let Dbal:=fun i=>2*((J i).card:ℝ)/dens
    let Dlevel:=fun i=>2*(Fintype.card (Z i):ℝ)/dens
    ∃weight:∀i,(Fin (r+4+1)→W i)→ℝ,
    (∀i≤L,SuccessorSequenceWeightConditions (G.comap (f i)) (ρi i) (3*d) (Dlevel i) τ
      (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weight i)) ∧
    (∀i x,f i (ρi i x)=π (f i x)) ∧
    ∀i≤L,
      M≤(I i).card ∧ M≤(J i).card ∧ M≤Fintype.card (W i) ∧ M≤Fintype.card (Z i) ∧
      (ρ₀/8)*(Fintype.card (W i):ℝ)≤Fintype.card (Z i) ∧ Fintype.card (Z i)≤Fintype.card (W i) ∧
      (I i).card≤Fintype.card (W i) ∧ (J i).card≤Fintype.card (W i) ∧
      (Fintype.card (W (i+1)):ℝ)≤ε*Fintype.card (W i) ∧
      (((I (i+1)).card:ℝ)≤ε*(I i).card) ∧ (((J (i+1)).card:ℝ)≤ε*(J i).card) ∧
      (∀x,ρi i x∈I i↔x∈I i) ∧
      (Fintype.card (W i):ℝ)≤K*(I i).card ∧ (Fintype.card (Z i):ℝ)≤K*(I i).card ∧
      (Fintype.card (W i):ℝ)≤K*(J i).card ∧
      (∀x:W i,|(((G.comap (f i)).neighborFinset x∩I i).card:ℝ)-Dbal i|≤δPbal*Fintype.card (W i)) ∧
      (∀x:W i,(1/2+γ)*(I i).card≤(((G.comap (f i)).neighborFinset x∩I i).card:ℝ)) ∧
      (∀x:W i,|((G.comap (f i)).degree x:ℝ)-Dlevel i|≤δP*Fintype.card (W i)) ∧
      (∀x:W i,(1/2+γ)*Fintype.card (W i)≤((G.comap (f i)).degree x:ℝ)) ∧
      (Fintype.card (W i):ℝ)/2≤Dlevel i ∧ Dlevel i≤2*Fintype.card (W i) ∧
      p*Dbal i=s₀*(J i).card ∧ k*Dbal i=(s₀/((r+4:ℕ):ℝ))*(J i).card ∧
      (Fintype.card (Z i):ℝ)*(s₀/((r+4:ℕ):ℝ))=Dlevel i*k ∧
      (Fintype.card (Z i):ℝ)*(s₀/((r+4:ℕ):ℝ))*((r+4:ℕ):ℝ)=Dlevel i*p :=by
  obtain ⟨K,hK,hlevels⟩:=marked_fixed_vortex_adaptive_level_inputs ε ρ₀ he he1 hρ₀
  obtain ⟨βmax,hβmax,hweights⟩:=marked_fixed_vortex_successor_weight_families k₀ (r+4) hlen α τ hα hτ hmargin
  obtain ⟨Nw,hNw,hweights⟩:=hweights (3*d)
  refine ⟨K,hK,βmax,hβmax,?_⟩
  intro β γ δPbal δP hb hb1 hbα hbmax hγ hγα hβbal hβP M
  obtain ⟨Mlevel,hMlevel,hlevels⟩:=hlevels β α γ δPbal δP r hb hb1 hα hbα hγ hγα hβbal hβP M
  let m₀:=max Mlevel ⌈2*(Nw:ℝ)/ε⌉₊
  refine ⟨m₀,by dsimp [m₀];omega,?_⟩
  intro V U _ _ _ _ G D m hreg hn hD hρlo hρhi hm Q π hpres L hL s₀ W Z f ρi I J dens p k Dbal Dlevel
  have hmLevel:Mlevel≤m:=(le_max_left _ _).trans hm
  have hceil:2*(Nw:ℝ)/ε≤m:=(Nat.le_ceil _).trans (by exact_mod_cast (show ⌈2*(Nw:ℝ)/ε⌉₊≤m from (le_max_right _ _).trans hm))
  have hsize:(Nw:ℝ)≤ε*m/2:=by
    have hh:2*(Nw:ℝ)≤(m:ℝ)*ε:=(div_le_iff₀ he).mp hceil
    nlinarith
  have hρ:0 < initialIndexDensity U D:=hρ₀.trans_le hρlo
  obtain ⟨weight,hweight⟩:=hweights V U G D m β ε Q hreg hn hD hρ hb hbmax he hsize π hpres L hL
  have hgeom:=hlevels V U G D m hreg hn hD hρlo hρhi hmLevel Q π hpres L hL s₀
  exact ⟨weight,hweight,hgeom⟩
end Oberwolfach
