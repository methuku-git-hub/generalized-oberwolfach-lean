module

public import Oberwolfach.OrdinaryExpandedFixedVortexAdaptiveHubWeights
public import Oberwolfach.OrdinaryFixedVortexHubSetupsBeforeSampling

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

/-! Choose the fixed fractional cycle weights from the host before sampling,
then add the adaptive hub-weight event to any prior on the same expanded sample. -/
theorem ordinary_expanded_vortex_adaptive_hub_weights_from_host
    (m:ℕ) (hm:2≤m) (α:ℝ) (hα:0<α):
    ∃c C:ℝ,0<c ∧ 0<C ∧
    ∀(d:ℕ) (hd:2≤d) (β ε ρ₀ pmin ξ b Bweight ηHub Kdom χ:ℝ),
      0≤β→β≤1/4→β≤α/8→0<ε→ε<1/4→0<ρ₀→0<pmin→pmin≤1→0<ξ→0<χ→
      1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom→b≤c→
      (4*C/pmin^(3*m+1))*Kdom^m≤Bweight→ξ+2*β<ηHub→
    ∃t ζ:ℝ,0<t ∧ 0<ζ ∧ ∃v₀:ℕ,1≤v₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∀(θhost:ℝ),1/2≤θhost→cycleThreshold (m+1)≤θhost→
      (θhost+α)*Fintype.card V≤D→
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (pH:ℝ),
      pmin≤2*p→pmin≤pH→pH≤1→2*p=initialIndexDensity U D*pH→
    ∀(Ledit density tR tH βe βh:ℕ→ℝ),
      (∀i,i<Q.length→0≤Ledit i ∧ Ledit i≤ζ*(markedVortexInnerVertices Q i).card)→
    ∀(q:U→Γ→ℝ) (hq:∀u z,0≤q u z) (hQ:∀u,∑z,q u z≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑z,q u z)) (j:Color),
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (κ:FiniteLaw (Sym2 V→Bool))
      (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V→Bool)→Prop) (a:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let J:RawWheelOutcome V U Γ Color→Prop:=fun σ=>∀i,i<Q.length→
      OrdinaryAdaptiveHubWeightsLevelEvent m (P.comap (markedVortexVertexEmbedding Q i))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) (markedVortexPermutation Q π hπ i) d
        (2*p) pH (density i) (tR i) (tH i) (Ledit i) (βe i) (βh i) b Bweight ηHub
        (fun z=>s (markedVortexHubEmbedding Q i z)) j
        (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ);
    1-a≤((μ.sigma ν).prod κ).probability E →
    1-a-χ≤((μ.sigma ν).prod κ).probability (fun z=>E z ∧ J (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) :=by
  obtain ⟨c,C,hc,hC,hsetup⟩:=ordinary_fixed_vortex_hub_setups_before_sampling m hm α hα
  refine ⟨c,C,hc,hC,?_⟩
  intro d hd β ε ρ₀ pmin ξ b Bweight ηHub Kdom χ hβ hβ1 hβα hε hε1 hρ₀ hpmin hpmin1 hξ hχ hKdom hb hB hgap
  have hK:2/ε≤Kdom:=by
    have he:(ε:ℝ)≠0:=ne_of_gt hε
    have heq:1/(ε/2)=2/ε:=by field_simp
    have hx:0≤1/((ε/2)*(ρ₀/8)):=by positivity
    rw [heq] at hKdom
    linarith
  obtain ⟨vSetup,hvSetup,hchoose⟩:=hsetup β ε ρ₀ pmin ξ b Bweight ηHub Kdom
    hβ hβ1 hβα hε hε1 hρ₀ hpmin hpmin1 hK hb hB hgap d
  obtain ⟨t,ζ,ht,hζ,vProb,hvProb,hprob⟩:=ordinary_expanded_fixed_vortex_adaptive_hub_weights m d hm hd
    β ε ρ₀ pmin ξ (2*((3*d:ℕ):ℝ)) c C b Bweight ηHub Kdom χ
    hβ hβ1 hε hε1 hρ₀ hpmin hξ hC hχ hKdom
  refine ⟨t,ζ,ht,hζ,max vSetup vProb,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hρlo hρhi hv Q π hπ hnoshort
    θhost hθ hthreshold hdegree p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq
    Ledit density tR tH βe βh hedit q hq hQ s hs hS j R _ ν κ E a μ J hE
  have hDhalf:(Fintype.card V:ℝ)/2≤D:=by
    have hh:=mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤θhost+α by linarith)
      (show (0:ℝ)≤Fintype.card V by positivity)
    nlinarith only [hh,hdegree]
  have hpR1:2*p≤1:=by linarith
  obtain ⟨weight,hw⟩:=hchoose V U P D vsize hreg hn hρlo hρhi (by omega) Q π hπ
    θhost (2*p) pH hθ hthreshold hdegree hpR hpR1 hpH hpH1 hpEq
  exact hprob V U Γ Color P D vsize hreg hn hDhalf hρlo hρhi (by omega) Q π hπ hnoshort
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH (fun i=>2*pH*(markedVortexInnerHubs Q i).card/(2*p))
    Ledit density tR tH βe βh weight hw hedit q hq hQ s hs hS j ν κ E a hE
end Oberwolfach
