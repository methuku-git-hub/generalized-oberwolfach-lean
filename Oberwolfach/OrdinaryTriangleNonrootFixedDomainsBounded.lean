module

public import Oberwolfach.OrdinaryDeepCoverLevelInputs
public import Oberwolfach.OrdinaryTriangleNonrootCoverBoundedProbability
public import Oberwolfach.OrdinaryRawPairRestriction
public import Oberwolfach.VortexCommonEvents

@[expose] public section
/-! The triangle cover events on all fixed shrinking domains hold together
on the same ambient raw sample. The per-domain host hypotheses are explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_nonroot_cover_fixed_domains_bounded
    (α p ω:ℝ)
    (hα:0<α) (hp:0<p) (hp1:p≤1) (hω:0<ω):
    ∃κ:ℝ,0<κ ∧ κ≤1 ∧ ∀(η χ:ℝ),0<η→η<1→0<χ→
    ∀Dmax d:ℕ,∀hd:2≤d,∃M₀:ℕ,1≤M₀ ∧
    ∀(V U Γ Color:Type) (W Z:ℕ→Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder U]
      [∀i,Fintype (W i)] [∀i,Fintype (Z i)] [∀i,LinearOrder (W i)] [∀i,LinearOrder (Z i)],
    ∀(P F:SimpleGraph V) (f:∀i,W i↪V) (g:∀i,Z i↪U) (π:∀i,Equiv.Perm (W i))
      (A:∀i,Finset (W i)) (J:∀i,Finset (Z i)) (L:ℕ),
      (∀i≤L,M₀≤(A i).card)→(∀i<L,((A (i+1)).card:ℝ)≤η*(A i).card)→
    ∀(pR pH:ℝ) (hpR:0≤pR) (hpR1:pR≤1) (D ε:ℕ→ℝ),
      (∀i≤L,OrdinaryDeepCoverLevelInputs 2 Dmax d α p ω κ κ (P.comap (f i))
        (F.comap (f i)) (π i) (J i) pR pH (D i) (ε i))→
    ∀(q:U→Γ→ℝ) (hq:∀u z,0≤q u z) (hQ:∀u,∑z,q u z≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑z,q u z)) (j:Color) (hj:∀u,s u j=pH),
    1-χ≤(FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>pR) (fun _=>hpR) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀i≤L,OrdinaryTriangleFiniteCoverNonrootDegreeEvent κ (P.comap (f i)) (F.comap (f i))
        (J i) (π i) d j (ordinaryRawRestrictPair (f i) (g i) σ)):=by
  obtain ⟨κ,hκ,hκ1,htriangle⟩:=ordinary_triangle_finite_cover_nonroot_degree_bounded_high_probability α p ω hα hp hp1 hω
  refine ⟨κ,hκ,hκ1,?_⟩
  intro η χ hη hη1 hχ Dmax d hd
  obtain ⟨N,hN⟩:=htriangle Dmax d 1 hd
  obtain ⟨M,hM⟩:=exists_nat_gt (1/((1-η)*χ))
  let M₀:=max N (max M 1)
  have hM0:1≤M₀:=by dsimp [M₀];omega
  have hM0pos:(0:ℝ)<M₀:=by exact_mod_cast (show 0<M₀ by omega)
  have hMχ:1/((1-η)*(M₀:ℝ))≤χ:=by
    have hden:0<(1-η)*χ:=mul_pos (by linarith) hχ
    have hle:(M:ℝ)≤M₀:=by exact_mod_cast (show M≤M₀ by dsimp [M₀];omega)
    have hbig:1/((1-η)*χ)≤(M₀:ℝ):=hM.le.trans hle
    have hh:1≤((1-η)*χ)*(M₀:ℝ):=by simpa only [mul_comm] using (div_le_iff₀ hden).mp hbig
    apply (div_le_iff₀ (mul_pos (by linarith) hM0pos)).mpr
    nlinarith only [hh]
  refine ⟨M₀,hM0,?_⟩
  intro V U Γ Color W Z _ _ _ _ _ _ _ _ _ _ P F f g π A J L hn hstep pR pH hpR hpR1 D ε hinput q hq hQ s hs hS j hj
  let μ:FiniteLaw (RawWheelOutcome V U Γ Color):=
    FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hpR) (fun _=>hpR1) d hd q hq hQ s hs hS)
  let Good:=fun i (σ:RawWheelOutcome V U Γ Color)=>
    OrdinaryTriangleFiniteCoverNonrootDegreeEvent κ (P.comap (f i)) (F.comap (f i))
      (J i) (π i) d j (ordinaryRawRestrictPair (f i) (g i) σ)
  have hpos:∀i≤L,0<((A i).card:ℝ):=by
    intro i hi
    exact_mod_cast (show 0<(A i).card by have hh:=hn i hi;omega)
  have hlast:(M₀:ℝ)≤((A L).card:ℝ):=by exact_mod_cast (hn L (by omega))
  have hprob:∀i≤L,1-1/((A i).card:ℝ)≤μ.probability (Good i):=by
    intro i hi
    let Local:=OrdinaryTriangleFiniteCoverNonrootDegreeEvent (Γ:=Γ) (Color:=Color) κ (P.comap (f i)) (F.comap (f i)) (J i) (π i) d j
    have hlaw:=ordinary_raw_pair_restriction_probability (f i) (f i).injective (g i) (g i).injective
      pR hpR hpR1 d hd q hq hQ s hs hS Local
    have hsize:N≤Fintype.card (W i):=by
      have hh:=hn i hi
      have hc:=Finset.card_le_univ (A i)
      dsimp [M₀] at hh
      omega
    have hi':=hinput i hi
    have hlocal:=hN (W i) (Z i) Γ Color (P.comap (f i)) (F.comap (f i)) (π i) (J i) hsize
      hi'.J_small hi'.hub_lower hi'.hub_upper hi'.min_degree hi'.conflict_degree hi'.conflict_contains hi'.no_short
      pR pH (D i) (ε i) hi'.pR_lower hi'.pR_upper hi'.pH_lower hi'.pH_upper hi'.density_lower
      hi'.error_nonneg hi'.error_upper hi'.approximate_regular hi'.balance_mean
      (fun z=>q (g i z)) (fun z=>hq (g i z)) (fun z=>hQ (g i z))
      (fun z=>s (g i z)) (fun z=>hs (g i z)) (fun z=>hS (g i z)) j (fun z=>hj (g i z))
    have hc:((A i).card:ℝ)≤Fintype.card (W i):=by exact_mod_cast Finset.card_le_univ (A i)
    have hinv:1/(Fintype.card (W i):ℝ)≤1/((A i).card:ℝ):=one_div_le_one_div_of_le (hpos i hi) hc
    change 1-1/((A i).card:ℝ)≤μ.probability (fun σ=>Local (ordinaryRawRestrictPair (f i) (g i) σ))
    rw [hlaw]
    simp only [pow_one] at hlocal
    linarith only [hinv,hlocal]
  have hcommon:=vortex_fixed_domain_common_event μ η (M₀:ℝ) hη hη1 hM0pos
    (fun i=>(A i).card) L hpos hstep hlast Good hprob
  exact le_trans (by linarith only [hMχ]) hcommon
end Oberwolfach
