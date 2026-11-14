module

public import Oberwolfach.OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent
public import Oberwolfach.OrdinaryRawPairRestriction
public import Oberwolfach.VortexUniformEvents

@[expose] public section
/-! Adaptive ordinary hub weights at all fixed shrinking domains on one
ambient sample. The deterministic weight setups are selected before sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 26000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_adaptive_hub_weights_inner_scale_fixed_domains
    (m d:ℕ) (hm:2≤m) (hd:2≤d)
    (pmin δ ξ Lconf cLo cHi b Bweight ηHub Ksetup t Kdom ε χ:ℝ)
    (hpmin:0<pmin) (hcHi:0<cHi) (ht:0<t)
    (hKdom:0≤Kdom) (hε:0<ε) (hε1:ε<1) (hχ:0<χ):
    ∃M₀:ℕ,1≤M₀ ∧ ∀(V U Γ Color:Type) (W Z:ℕ→Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
      [∀i,Fintype (W i)] [∀i,Fintype (Z i)] [∀i,LinearOrder (W i)] [∀i,DecidableEq (Z i)],
    ∀(P F:SimpleGraph V) (f:∀i,W i↪V) (g:∀i,Z i↪U) (π:∀i,Equiv.Perm (W i))
      (A:∀i,Finset (W i)) (B:∀i,Finset (Z i)) (L:ℕ),
      (∀i≤L,M₀≤(A i).card)→(∀i<L,((A (i+1)).card:ℝ)≤ε*(A i).card)→
      (∀i≤L,(Fintype.card (Z i):ℝ)≤Kdom*(A i).card)→
      (∀i≤L,permutationConflictGraph (π i) (3*d)≤F.comap (f i))→
      (∀i≤L,∀x l,0<l→l<2*d+1→((π i)^l) x≠x)→
    ∀(pR pH:ℝ) (hpR:0≤pR) (hpR1:pR≤1)
      (D Ledit density tR tH βe βh:ℕ→ℝ)
      (weight:∀i,OrdinaryCycle ((P.comap (f i)).induce ((A i):Set (W i))) (m+1)→ℝ),
      (∀i≤L,OrdinaryInnerHubWeightSetupGeneral m (P.comap (f i)) (F.comap (f i)) (A i) (weight i)
        pmin pR pH (D i) δ ξ Lconf cLo cHi b Bweight ηHub Ksetup)→
    let Bpot:=4*cHi/pmin^(3*m+1);
    (∀i≤L,t+((m+1:ℕ):ℝ)^2*Bpot*(Ledit i)/(A i).card+
      2*(3*((m+1:ℕ):ℝ)^4*Bpot*(Ledit i)/(A i).card)≤ξ)→
    ∀(q:U→Γ→ℝ) (hq:∀u z,0≤q u z) (hQ:∀u,∑z,q u z≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑z,q u z)) (j:Color),
    1-χ≤(FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>pR) (fun _=>hpR) (fun _=>hpR1)
      d hd q hq hQ s hs hS)).probability (fun σ=>∀i≤L,
      OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent m (P.comap (f i)) (F.comap (f i)) (A i) (B i) (π i) d
        pR pH (density i) (tR i) (tH i) (Ledit i) (βe i) (βh i) cLo (4*cHi/pmin^(3*m+1)) ηHub (fun z=>s (g i z)) j
        (ordinaryRawRestrictPair (f i) (g i) σ)):=by
  let Bpot:ℝ:=4*cHi/pmin^(3*m+1)
  let Cden:ℝ:=(4*(d:ℝ)+3)^2*((((m+1:ℕ):ℝ)^4)*Bpot)*
    (2*((m+1:ℕ):ℝ))*((((m+1:ℕ):ℝ)^2)*Bpot)
  let c:ℝ:=2*t^2/Cden
  have hBpot:0<Bpot:=by dsimp [Bpot];positivity
  have hCden:0<Cden:=by dsimp [Cden];positivity
  have hc:0<c:=by dsimp [c];positivity
  obtain ⟨M₀,hM₀,hcommon⟩:=vortex_exponential_common_event (2*Kdom) c ε χ 2 hc hε hε1 hχ
  refine ⟨M₀,hM₀,?_⟩
  intro V U Γ Color W Z _ _ _ _ _ _ _ _ _ _ P F f g π A B L hsize hstep hZ hconf hnoshort
    pR pH hpR hpR1 D Ledit density tR tH βe βh weight hsetup Bpot' hmargin q hq hQ s hs hS j
  let μ:FiniteLaw (RawWheelOutcome V U Γ Color):=
    FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hpR) (fun _=>hpR1) d hd q hq hQ s hs hS)
  let Good:=fun i (σ:RawWheelOutcome V U Γ Color)=>
    OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent m (P.comap (f i)) (F.comap (f i)) (A i) (B i) (π i) d
      pR pH (density i) (tR i) (tH i) (Ledit i) (βe i) (βh i) cLo (4*cHi/pmin^(3*m+1)) ηHub (fun z=>s (g i z)) j
      (ordinaryRawRestrictPair (f i) (g i) σ)
  apply hcommon (RawWheelOutcome V U Γ Color) μ (fun i=>(A i).card) L hsize hstep Good
  intro i hi
  let Local:=OrdinaryAdaptiveHubWeightsInnerScaleLevelEvent (Γ:=Γ) m (P.comap (f i)) (F.comap (f i)) (A i) (B i) (π i) d
    pR pH (density i) (tR i) (tH i) (Ledit i) (βe i) (βh i) cLo (4*cHi/pmin^(3*m+1)) ηHub (fun z=>s (g i z)) j
  have hlaw:=ordinary_raw_pair_restriction_probability (f i) (f i).injective (g i) (g i).injective
    pR hpR hpR1 d hd q hq hQ s hs hS Local
  have hA:(0:ℝ)<(A i).card:=by exact_mod_cast (show 0<(A i).card by have hh:=hsize i hi;omega)
  have hcard:Fintype.card ((A i):Set (W i))=(A i).card:=by simp
  have hexp: -2*t^2/((4*(d:ℝ)+3)^2*((((m+1:ℕ):ℝ)^4)*Bpot/(A i).card)*
      (2*((m+1:ℕ):ℝ))*((((m+1:ℕ):ℝ)^2)*Bpot)) = -c*(A i).card:=by
    dsimp [c,Cden]
    field_simp [hA.ne',hCden.ne']
    <;> ring
  have hlocal:=ordinary_adaptive_hub_weights_inner_scale_raw_probability m hm (P.comap (f i)) (F.comap (f i))
    (A i) (B i) (π i) d hd j (hconf i hi) (hnoshort i hi)
    pmin pR pH (D i) δ ξ Lconf cLo cHi b Bweight ηHub Ksetup t (Ledit i) (density i) (tR i) (tH i) (βe i) (βh i)
    hcHi ht (weight i) (hsetup i hi) (fun z=>q (g i z)) (fun z=>hq (g i z)) (fun z=>hQ (g i z))
    (fun z=>s (g i z)) (fun z=>hs (g i z)) (fun z=>hS (g i z))
    (by simpa only [hcard] using hmargin i hi)
  have hz:(A i).card*(Fintype.card (Z i):ℝ)≤Kdom*((A i).card:ℝ)^2:=by
    have hh:=mul_le_mul_of_nonneg_left (hZ i hi) hA.le
    nlinarith only [hh]
  have herr:(Fintype.card ((A i):Set (W i)):ℝ)*Fintype.card (Z i)*
      (2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((((m+1:ℕ):ℝ)^4)*Bpot/Fintype.card ((A i):Set (W i)))*
        (2*((m+1:ℕ):ℝ))*((((m+1:ℕ):ℝ)^2)*Bpot))))≤
      (2*Kdom)*((A i).card:ℝ)^2*Real.exp (-c*(A i).card):=by
    rw [hcard,hexp]
    have hh:=mul_le_mul_of_nonneg_right hz (Real.exp_pos (-c*(A i).card)).le
    nlinarith only [hh]
  change 1-(2*Kdom)*((A i).card:ℝ)^2*Real.exp (-c*(A i).card)≤
    μ.probability (fun σ=>Local (ordinaryRawRestrictPair (f i) (g i) σ))
  rw [hlaw]
  have hlocal':1-(Fintype.card ((A i):Set (W i)):ℝ)*Fintype.card (Z i)*
      (2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((((m+1:ℕ):ℝ)^4)*Bpot/Fintype.card ((A i):Set (W i)))*
        (2*((m+1:ℕ):ℝ))*((((m+1:ℕ):ℝ)^2)*Bpot))))≤
      (FiniteLaw.pi (rawWheelLaw (V:=W i) (fun _=>pR) (fun _=>hpR) (fun _=>hpR1) d hd
        (fun z=>q (g i z)) (fun z=>hq (g i z)) (fun z=>hQ (g i z))
        (fun z=>s (g i z)) (fun z=>hs (g i z)) (fun z=>hS (g i z)))).probability Local
      :=by convert hlocal using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  linarith only [herr,hlocal']
end Oberwolfach
