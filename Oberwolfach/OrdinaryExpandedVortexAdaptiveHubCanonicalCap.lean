module

public import Oberwolfach.OrdinaryExpandedVortexAdaptiveHubWeightsHostEarlyEdit
public import Oberwolfach.OrdinaryVortexCanonicalEditCapSmall

@[expose] public section
/-! A fixed geometric edit cap gives the same-sample adaptive hub-weight
event without assuming a separate budget at each level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expanded_vortex_adaptive_hub_weights_canonical_cap
    (m:ℕ) (hm:2≤m) (α:ℝ) (hα:0<α):
    ∃c C:ℝ,0<c ∧ 0<C ∧
    ∀(d:ℕ) (hd:2≤d) (ε ρ₀ pmin ξ b Bweight ηHub Kdom χ:ℝ),
      0<ε→ε<1/4→0<ρ₀→0<pmin→pmin≤1→0<ξ→0<χ→
      1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom→b≤c→
      (4*C/pmin^(3*m+1))*Kdom^m≤Bweight→
    ∃t ζ:ℝ,0<t ∧ 0<ζ ∧ ∀δcap:ℝ,0≤δcap→δcap≤ζ/2→∀β:ℝ,0≤β→β≤1/4→β≤α/8→ξ+2*β<ηHub→∃v₀:ℕ,1≤v₀ ∧
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
    ∀(density tR tH βe βh:ℕ→ℝ),
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
        (2*p) pH (density i) (tR i) (tH i) (2*((3*d:ℕ):ℝ)+δcap*min ((markedVortexInnerVertices Q i).card:ℝ) (markedVortexInnerHubs Q i).card) (βe i) (βh i) b Bweight ηHub
        (fun z=>s (markedVortexHubEmbedding Q i z)) j
        (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ);
    1-a≤((μ.sigma ν).prod κ).probability E →
    1-a-χ≤((μ.sigma ν).prod κ).probability (fun z=>E z ∧ J (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) :=by
  obtain ⟨c,C,hc,hC,hmain⟩:=ordinary_expanded_vortex_adaptive_hub_weights_from_host_early_edit m hm α hα
  refine ⟨c,C,hc,hC,?_⟩
  intro d hd ε ρ₀ pmin ξ b Bweight ηHub Kdom χ hε hε1 hρ₀ hpmin hpmin1 hξ hχ hKdom hb hB
  obtain ⟨t,ζ,ht,hζ,hprob⟩:=hmain d hd ε ρ₀ pmin ξ b Bweight ηHub Kdom χ
    hε hε1 hρ₀ hpmin hpmin1 hξ hχ hKdom hb hB
  refine ⟨t,ζ,ht,hζ,?_⟩
  intro δcap hδcap hδζ β hβ hβ1 hβα hgap
  obtain ⟨vp,hvp,hprob⟩:=hprob β hβ hβ1 hβα hgap
  obtain ⟨vs,hvs,hsmall⟩:=ordinary_vortex_canonical_edit_cap_small ε ρ₀ ζ δcap d
    hε hε1 hρ₀ hζ hδcap hδζ β hβ hβ1
  refine ⟨max vp vs,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hρlo hρhi hv Q π hπ hnoshort
    θhost hθ hthreshold hdegree p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq
    density tR tH βe βh q hq hQ s hs hS j R _ ν κ E a μ J hE
  have hDhalf:(Fintype.card V:ℝ)/2≤D:=by
    have hh:=mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤θhost+α by linarith)
      (show (0:ℝ)≤Fintype.card V by positivity)
    nlinarith only [hh,hdegree]
  let Ledit:ℕ→ℝ:=fun i=>2*((3*d:ℕ):ℝ)+δcap*min ((markedVortexInnerVertices Q i).card:ℝ) (markedVortexInnerHubs Q i).card
  have hedit:∀i,i<Q.length→0≤Ledit i ∧ Ledit i≤ζ*(markedVortexInnerVertices Q i).card:=by
    intro i hi
    exact hsmall V U P D vsize hreg hn hDhalf hρlo hρhi (by omega) Q i hi
  exact hprob V U Γ Color P D vsize hreg hn hρlo hρhi (by omega) Q π hπ hnoshort
    θhost hθ hthreshold hdegree p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq
    Ledit density tR tH βe βh hedit q hq hQ s hs hS j ν κ E a hE
end Oberwolfach
