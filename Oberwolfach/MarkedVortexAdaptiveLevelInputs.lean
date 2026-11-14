module

public import Oberwolfach.MarkedFixedVortexBaselineGeometry
public import Oberwolfach.MarkedFixedVortexCanonicalDensities
public import Oberwolfach.MarkedVortexNeighbourhoodSizeInputs
public import Oberwolfach.MarkedVortexNeighbourhoodConstant
public import Oberwolfach.MarkedVortexAdaptiveDegreeInputs

@[expose] public section
/-! Simultaneous geometric, size, degree and exact-density inputs on a fixed vortex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_fixed_vortex_adaptive_level_inputs
    (ε ρ₀:ℝ) (he:0<ε) (he1:ε<1/4) (hρ₀:0<ρ₀):
    ∃K:ℝ,1≤K ∧ ∀ (β α γ δPbal δP:ℝ) (r:ℕ),
    0≤β → β≤1/4 → 0<α → β≤α/8 → 0≤γ → γ≤α/2 → β≤δPbal → β≤δP →
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
  obtain ⟨K,hK1,hKI,hKJ⟩:=marked_vortex_neighbourhood_constant_exists ε ρ₀ he hρ₀
  refine ⟨K,hK1,?_⟩
  intro β α γ δPbal δP r hb hb1 hα hbα hγ hγα hβbal hβP M
  obtain ⟨m₀,hm₀,hbase⟩:=marked_fixed_vortex_baseline_geometry β ε ρ₀ hb hb1 he he1 hρ₀ M
  refine ⟨m₀,hm₀,?_⟩
  intro V U _ _ _ _ G D m hreg hn hD hρlo hρhi hm Q π hpres L hL s₀ W Z f ρi I J dens p k Dbal Dlevel
  have hDhalf:(Fintype.card V:ℝ)/2≤D:=by
    have hn0:(0:ℝ)≤Fintype.card V:=Nat.cast_nonneg _
    nlinarith [mul_nonneg hα.le hn0]
  have hmpos:0<m:=by omega
  have hρ:0<dens:=hρ₀.trans_le hρlo
  have hGeom:=hbase V U G D m hreg hn hDhalf hρlo hρhi hm Q π hpres L hL
  have hNbr:=marked_vortex_neighbourhood_size_inputs Q hreg hn hDhalf hρ₀ hρlo hρhi hb hb1 he (by linarith) hmpos K (by linarith) hKI hKJ L hL
  have hDeg:=marked_vortex_adaptive_degree_inputs Q hreg hn hD hα hρ hb hbα hb1 he hmpos γ δPbal δP hγ hγα hβbal hβP L hL
  have hDen:=marked_fixed_vortex_canonical_densities G D m r β ε ρ₀ s₀ Q hρ₀ hρlo
  refine ⟨hGeom.1,?_⟩
  intro i hi
  obtain ⟨hI,hJ,hW,hZ,hZlo,hZhi,hIhi,hJhi,hWstep,hTI,hRJ,hTsize,hRsize,hIstep,hJstep,hIinv,hTinv⟩:=hGeom.2 i hi
  obtain ⟨hWI,hZI,hWJ⟩:=hNbr i hi
  obtain ⟨hDbal,hImin,hDlevel,hWmin,hDlo,hDhi⟩:=hDeg i hi
  obtain ⟨hDp,hDk,hLk,hLp⟩:=hDen i
  exact ⟨hI,hJ,hW,hZ,hZlo,hZhi,hIhi,hJhi,hWstep,hIstep,hJstep,hIinv,hWI,hZI,hWJ,hDbal,hImin,hDlevel,hWmin,hDlo,hDhi,hDp,hDk,hLk,hLp⟩
end Oberwolfach
