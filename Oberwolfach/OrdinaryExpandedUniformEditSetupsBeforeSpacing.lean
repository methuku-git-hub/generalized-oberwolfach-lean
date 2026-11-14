module

public import Oberwolfach.OrdinaryExpandedUniformEditBeforeSpacing
public import Oberwolfach.OrdinaryFixedVortexHubSetupsBeforeSampling

@[expose] public section
/-! Select fixed fractional cycle weights on the actual vortex before the
expanded sample, and add the all-edit weight event to any prior event on
that same expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expanded_uniform_edit_event_with_setups_before_spacing
    (m:ℕ) (hm:2 ≤ m) (α:ℝ) (hα:0<α):
    ∃c C:ℝ,0<c ∧ 0<C ∧
    ∀(ε ρ₀ pmin ξ b Bweight ηHub Kdom χ eParent hParent:ℝ),
      0<ε  →  ε<1/4  →  0<ρ₀  →  0<pmin  →  pmin ≤ 1  →  0<ξ  →  0<χ  → 
      2/ε ≤ Kdom  →  1+1/(ε/2)+1/((ε/2)*(ρ₀/8)) ≤ Kdom  → 
      b ≤ c  →  (4*C/pmin^(3*m+1))*Kdom^m ≤ Bweight  →  0<eParent  →  0<hParent  → 
    ∃t eEvent hEvent cap:ℝ,0<t ∧ 0<eEvent ∧ 0<hEvent ∧ 0<cap ∧
      eEvent ≤ eParent ∧ hEvent ≤ hParent ∧
    ∀(d:ℕ) (hd:2 ≤ d),∀β:ℝ,0 ≤ β  →  β ≤ 1/4  →  β ≤ α/8  →  ξ+2*β<ηHub  →  ∃v₀:ℕ,1 ≤ v₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D  →  0<Fintype.card V  → 
      ρ₀ ≤ initialIndexDensity U D  →  initialIndexDensity U D ≤ 1  →  v₀ ≤ vsize  → 
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x l,0<l  →  l<2*d+1  →  (π^l) x≠x)  → 
    ∀(θhost p k p₂ k₂ u:ℝ) (hθ:1/2 ≤ θhost) (hthreshold:cycleThreshold (m+1) ≤ θhost)
      (hdegree:(θhost+α)*Fintype.card V ≤ D)
      (hp:0 ≤ p) (hk:0 ≤ k) (hp₂:0 ≤ p₂) (hk₂:0 ≤ k₂) (hu:0 ≤ u) (hsum:2*p+2*k+2*p₂+2*k₂+u ≤ 1),
    ∀(pH:ℝ),pmin ≤ 2*p  →  2*p ≤ 1  →  pmin ≤ pH  →  pH ≤ 1  →  2*p=initialIndexDensity U D*pH  → 
    ∃weight:∀i,OrdinaryCycle ((P.comap (markedVortexVertexEmbedding Q i)).induce
        ((markedVortexInnerVertices Q i):Set (markedVortexVertexType Q i))) (m+1) → ℝ,
    (∀i,i<Q.length  →  OrdinaryInnerHubWeightSetupGeneral m (P.comap (markedVortexVertexEmbedding Q i))
      ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
      (markedVortexInnerVertices Q i) (weight i) pmin (2*p) pH
      (2*pH*(markedVortexInnerHubs Q i).card/(2*p)) β ξ (2*((3*d:ℕ):ℝ)) c C b Bweight ηHub Kdom) ∧
    ∀(density tR tH:ℕ → ℝ) (q:U → Γ → ℝ) (hq:∀u z,0 ≤ q u z) (hQ:∀u,∑z,q u z ≤ 1/8)
      (s:U → Color → ℝ) (hs:∀u j,0 ≤ s u j)
      (hS:∀u,∑j,s u j ≤ intervalUncoveredProbability d (∑z,q u z)) (j:Color),
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) → Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (κ:FiniteLaw (Sym2 V → Bool))
      (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V → Bool) → Prop) (a:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let J:RawWheelOutcome V U Γ Color → Prop:=fun σ=>∀i,i<Q.length  →  ∀Lold:ℝ,
      0 ≤ Lold  →  Lold ≤ cap*(markedVortexInnerVertices Q i).card  → 
      OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent m (P.comap (markedVortexVertexEmbedding Q i))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) (markedVortexPermutation Q π hπ i) d
        (2*p) pH (density i) (tR i) (tH i) Lold (eParent*ε) (hParent*ε) c (4*C/pmin^(3*m+1)) ηHub
        (fun z=>s (markedVortexHubEmbedding Q i z)) j
        (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ);
    1-a ≤ ((μ.sigma ν).prod κ).probability E  → 
    1-a-χ ≤ ((μ.sigma ν).prod κ).probability (fun z=>E z ∧ J (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) :=by
  obtain ⟨c,C,hc,hC,hsetup⟩:=ordinary_fixed_vortex_hub_setups_before_sampling m hm α hα
  refine ⟨c,C,hc,hC,?_⟩
  intro ε ρ₀ pmin ξ b Bweight ηHub Kdom χ eParent hParent hε hε1 hρ₀ hpmin hpmin1 hξ hχ
    hK hKdom hb hB he hh
  obtain ⟨t,eEvent,hEvent,cap,ht,heEvent,hhEvent,hcap,heBound,hhBound,hprob⟩:=
    ordinary_expanded_fixed_vortex_uniform_edit_weights_before_spacing m hm ε ρ₀ pmin ξ
      c C b Bweight ηHub Kdom χ eParent hParent hε hε1 hρ₀ hpmin hξ hC hχ hKdom he hh
  refine ⟨t,eEvent,hEvent,cap,ht,heEvent,hhEvent,hcap,heBound,hhBound,?_⟩
  intro d hd β hβ hβ1 hβα hgap
  obtain ⟨v1,hv1,hprob⟩:=hprob d hd (2*((3*d:ℕ):ℝ)) β hβ hβ1
  obtain ⟨v2,hv2,hsetup⟩:=hsetup β ε ρ₀ pmin ξ b Bweight ηHub Kdom hβ hβ1 hβα hε hε1 hρ₀
    hpmin hpmin1 hK hb hB hgap d
  refine ⟨max v1 v2,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hρlo hρhi hv Q π hπ hnoshort
    θhost p k p₂ k₂ u hθ hthreshold hdegree hp hk hp₂ hk₂ hu hsum pH hpR hpR1 hpH hpH1 hpEq
  have hD:(Fintype.card V:ℝ)/2 ≤ D:=by
    have hn0:(0:ℝ) ≤ Fintype.card V:=by positivity
    nlinarith [mul_nonneg hα.le hn0,mul_nonneg (show 0 ≤ θhost-1/2 by linarith) hn0]
  obtain ⟨weight,hweight⟩:=hsetup V U P D vsize hreg hn hρlo hρhi (by omega) Q π hπ θhost (2*p) pH
    hθ hthreshold hdegree hpR hpR1 hpH hpH1 hpEq
  refine ⟨weight,hweight,?_⟩
  intro density tR tH q hq hQ s hs hS j R _ ν κ E a μ J hE
  exact hprob V U Γ Color P D vsize hreg hn hD hρlo hρhi (by omega) Q π hπ hnoshort
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH (fun i=>2*pH*(markedVortexInnerHubs Q i).card/(2*p))
    density tR tH weight hweight q hq hQ s hs hS j ν κ E a hE
end Oberwolfach
