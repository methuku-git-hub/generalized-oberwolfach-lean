module

public import Oberwolfach.OrdinaryVortexPresampleWeightsAndWindow
public import Oberwolfach.OrdinaryExpandedFixedVortexAdaptiveHubWeightsEarlyEdit

@[expose] public section
/-! Choose cycle weights and recent-edit budgets before sampling, then attach
all level hub-weight events to a pre-existing event on the same outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expanded_hub_weights_presample_weighted_prior
    (m d buffer:ℕ) (hm:2≤m) (hd:2≤d) (hbuffer:2≤buffer)
    (α ε ρ₀ pmin:ℝ) (hα:0<α) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀)
    (hpmin:0<pmin) (hpmin1:pmin≤1):
    ∃c C:ℝ,0<c ∧ 0<C ∧
    ∀(ξ b Bweight ηHub Kdom χ η:ℝ),0<ξ→0<χ→0<η→
      1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom→b≤c→
      (4*C/pmin^(3*m+1))*Kdom^m≤Bweight→ξ<ηHub→
    ∃t ζ δ rate:ℝ,0<t ∧ 0<ζ ∧ 0<δ ∧ δ≤α ∧ 0<rate ∧
    ∀β:ℝ,0≤β→β≤1/4→β≤α/8→β≤δ→ξ+2*β<ηHub→
    ∀Ccost:ℝ,0≤Ccost→∃v₀:ℕ,1≤v₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (θhost pH:ℝ),
      1/2≤θhost→cycleThreshold (m+1)≤θhost→(θhost+α)*Fintype.card V≤D→
      pmin≤2*p→pmin≤pH→pH≤1→2*p=initialIndexDensity U D*pH→
    ∀(density tR tH βe βh cost:ℕ→ℝ),
      (∀i,i+1<Q.length→∀j∈Finset.Icc (i+2-buffer) i,0≤cost j ∧
        cost j≤4*rate*Fintype.card (markedVortexVertexType Q j⊕markedVortexHubType Q j)+Ccost)→
    ∀(q:U→Γ→ℝ) (hq:∀u z,0≤q u z) (hQ:∀u,∑z,q u z≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑z,q u z)) (j:Color),
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (κ:FiniteLaw (Sym2 V→Bool))
      (E:(∀i,OrdinaryCycle ((P.comap (markedVortexVertexEmbedding Q i)).induce
        ((markedVortexInnerVertices Q i):Set (markedVortexVertexType Q i))) (m+1)→ℝ)→
        (Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V→Bool)→Prop) (a:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    (∀weight:∀i,OrdinaryCycle ((P.comap (markedVortexVertexEmbedding Q i)).induce
        ((markedVortexInnerVertices Q i):Set (markedVortexVertexType Q i))) (m+1)→ℝ,
      (∀i,i<Q.length→OrdinaryInnerHubWeightSetupGeneral m (P.comap (markedVortexVertexEmbedding Q i))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (weight i) pmin (2*p) pH
        (2*pH*(markedVortexInnerHubs Q i).card/(2*p)) β ξ (2*((3*d:ℕ):ℝ)) c C b Bweight ηHub Kdom)→
      1-a≤((μ.sigma ν).prod κ).probability (E weight)) →
    ∃weight:∀i,OrdinaryCycle ((P.comap (markedVortexVertexEmbedding Q i)).induce
        ((markedVortexInnerVertices Q i):Set (markedVortexVertexType Q i))) (m+1)→ℝ,
    let J:RawWheelOutcome V U Γ Color→Prop:=fun σ=>∀i,i<Q.length→
      OrdinaryAdaptiveHubWeightsLevelEvent m (P.comap (markedVortexVertexEmbedding Q i))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) (markedVortexPermutation Q π hπ i) d
        (2*p) pH (density i) (tR i) (tH i) (ordinaryVortexWindowEditBudget d buffer cost i) (βe i) (βh i) b Bweight ηHub
        (fun z=>s (markedVortexHubEmbedding Q i z)) j
        (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ);
    (∀i,i<Q.length→OrdinaryInnerHubWeightSetupGeneral m (P.comap (markedVortexVertexEmbedding Q i))
      ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
      (markedVortexInnerVertices Q i) (weight i) pmin (2*p) pH
      (2*pH*(markedVortexInnerHubs Q i).card/(2*p)) β ξ (2*((3*d:ℕ):ℝ)) c C b Bweight ηHub Kdom) ∧
    1-a-χ≤((μ.sigma ν).prod κ).probability (fun z=>E weight z ∧ J (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) :=by
  obtain ⟨c,C,hc,hC,hpre⟩:=ordinary_vortex_presample_weights_and_window m d buffer hm hbuffer α ε ρ₀ pmin hα hε hε1 hρ₀ hpmin hpmin1
  refine ⟨c,C,hc,hC,?_⟩
  intro ξ b Bweight ηHub Kdom χ η hξ hχ hη hK hb hB hgap
  obtain ⟨t,ζ,ht,hζ,hevent⟩:=ordinary_expanded_fixed_vortex_adaptive_hub_weights_early_edit m d hm hd ε ρ₀ pmin ξ
    (2*((3*d:ℕ):ℝ)) c C b Bweight ηHub Kdom χ hε hε1 hρ₀ hpmin hξ hC hχ hK
  obtain ⟨δ,rate,hδ,hδα,hrate,hpre⟩:=hpre η ζ hη hζ
  refine ⟨t,ζ,δ,rate,ht,hζ,hδ,hδα,hrate,?_⟩
  intro β hβ hβ1 hβα hβδ hgap' Ccost hCcost
  have hK':2/ε≤Kdom:=by
    have hp:0<ε/2:=by positivity
    have hr:0<ρ₀/8:=by positivity
    have hn:0≤1/((ε/2)*(ρ₀/8)):=by positivity
    have heq:1/(ε/2)=2/ε:=by field_simp
    linarith only [hK,hn,heq]
  obtain ⟨v₁,hv₁,hpre⟩:=hpre β ξ b Bweight ηHub Kdom hβ hβ1 hβα hβδ hK' hb hB hgap' Ccost hCcost
  obtain ⟨v₂,hv₂,hevent⟩:=hevent β hβ hβ1
  refine ⟨max v₁ v₂,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv Q π hπ hnoshort
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum θhost pH hθ hthreshold hdegree hpR hpH hpH1 hpEq
    density tR tH βe βh cost hcost q hq hQ s hs hS j R _ ν κ E a μ hE
  have hpR1:2*p≤1:=by linarith
  obtain ⟨weight,hsetup,hedit⟩:=hpre V U P D vsize hreg hn hD hρlo hρhi (by omega) Q π hπ θhost (2*p) pH
    hθ hthreshold hdegree hpR hpR1 hpH hpH1 hpEq cost hcost
  refine ⟨weight,hsetup,?_⟩
  exact hevent V U Γ Color P D vsize hreg hn hD hρlo hρhi (by omega) Q π hπ hnoshort
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH (fun i=>2*pH*(markedVortexInnerHubs Q i).card/(2*p))
    (ordinaryVortexWindowEditBudget d buffer cost) density tR tH βe βh weight hsetup hedit q hq hQ s hs hS j ν κ (E weight) a (hE weight hsetup)
end Oberwolfach
