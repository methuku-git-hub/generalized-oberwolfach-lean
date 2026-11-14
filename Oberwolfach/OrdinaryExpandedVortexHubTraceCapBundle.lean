module

public import Oberwolfach.OrdinaryExpandedVortexAdaptiveHubCanonicalCap
public import Oberwolfach.OrdinaryVortexTraceCapCostWitness

@[expose] public section
/-! Select one cap and one rate before the vortex error and host; the same
cap governs the high-probability hub event and every protected trace. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expanded_vortex_hub_trace_cap_bundle
    (m:ℕ) (hm:2≤m) (α:ℝ) (hα:0<α):
    ∃c C:ℝ,0<c ∧ 0<C ∧
    ∀(d:ℕ) (hd:2≤d) (ε ρ₀ pmin ξ b Bweight ηHub Kdom χ ηbal:ℝ),
      0<ε→ε<1/4→0<ρ₀→0<pmin→pmin≤1→0<ξ→0<χ→0<ηbal→
      1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom→b≤c→
      (4*C/pmin^(3*m+1))*Kdom^m≤Bweight→
    ∃t ζ δ δcap rate:ℝ,0<t ∧ 0<ζ ∧ 0<δ ∧ δ≤α ∧ 0<δcap ∧ δcap≤ζ/2 ∧ 0<rate ∧
    OrdinaryVortexTraceCapCostWitness ε ρ₀ α pmin pmin ηbal ζ δ δcap rate d ∧
    ∀β:ℝ,0≤β→β≤1/4→β≤α/8→β≤δ→ξ+2*β<ηHub→∃v₀:ℕ,1≤v₀ ∧
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
  obtain ⟨c,C,hc,hC,hmain⟩:=ordinary_expanded_vortex_adaptive_hub_weights_canonical_cap m hm α hα
  refine ⟨c,C,hc,hC,?_⟩
  intro d hd ε ρ₀ pmin ξ b Bweight ηHub Kdom χ ηbal hε hε1 hρ₀ hpmin hpmin1 hξ hχ hηbal hKdom hb hB
  obtain ⟨t,ζ,ht,hζ,hprob⟩:=hmain d hd ε ρ₀ pmin ξ b Bweight ηHub Kdom χ
    hε hε1 hρ₀ hpmin hpmin1 hξ hχ hKdom hb hB
  obtain ⟨δ,δcap,rate,hδ,hδα,hδcap,hδζ,hrate,htrace⟩:=
    ordinary_vortex_trace_cap_cost_witness ε ρ₀ α pmin pmin ηbal ζ d hε hε1 hρ₀ hα hpmin hpmin hηbal hζ
  refine ⟨t,ζ,δ,δcap,rate,ht,hζ,hδ,hδα,hδcap,hδζ,hrate,htrace,?_⟩
  intro β hβ hβ1 hβα hβδ hgap
  exact hprob δcap hδcap.le hδζ β hβ hβ1 hβα hgap
end Oberwolfach
