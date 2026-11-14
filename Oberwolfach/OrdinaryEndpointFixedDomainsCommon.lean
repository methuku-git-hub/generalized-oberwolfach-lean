module

public import Oberwolfach.EndpointPhysicalParentPotentialEvent
public import Oberwolfach.OrdinaryRawPairRestriction
public import Oberwolfach.VortexCommonEvents

@[expose] public section
/-! Choose the endpoint parent weights on each fixed shrinking domain before
sampling, then obtain their potential tests on one common raw sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_endpoint_fixed_domains_common
    (K ω p₀ t ε χ:ℝ) (hK:1≤K) (hω:0<ω) (hp₀:0<p₀) (ht:0<t)
    (hε:0<ε) (hε1:ε<1) (hχ:0<χ) (d:ℕ) (hd:2≤d):
    ∃M₀:ℕ,1≤M₀ ∧
    ∀(V U Γ Color:Type) (W Z:ℕ→Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder U]
      [∀i,Fintype (W i)] [∀i,Fintype (Z i)] [∀i,LinearOrder (W i)] [∀i,LinearOrder (Z i)],
    ∀(P F:SimpleGraph V) (f:∀i,W i↪V) (g:∀i,Z i↪U) (π:∀i,Equiv.Perm (W i))
      (A:∀i,Finset (W i)) (B:∀i,Finset (Z i)) (L:ℕ),
      (∀i≤L,M₀≤(A i).card)→(∀i<L,((A (i+1)).card:ℝ)≤ε*(A i).card)→
      (∀i≤L,(Fintype.card (W i):ℝ)≤K*(A i).card)→
      (∀i≤L,(Fintype.card (Z i):ℝ)≤K*(A i).card)→
      (∀i≤L,ω*(A i).card≤(B i).card)→
      (∀i≤L,∀x∈(A i)ᶜ,∀v∈insert x (A i),
        (3/4:ℝ)*(A i).card≤(((A i)∩(P.comap (f i)).neighborFinset v).card:ℝ))→
      (∀i≤L,permutationConflictGraph (π i) (3*d)≤F.comap (f i))→
      (∀i≤L,∀x k,0<k→k<2*d+1→((π i)^k) x≠x)→
    ∃weight:∀i,W i→Sym2 (W i⊕Z i)→ℝ,
      (∀i≤L,EndpointPhysicalParentWeights (P.comap (f i)) (A i) (A i)ᶜ (weight i)) ∧
    ∀(pR pH:ℝ) (hpR: p₀≤pR) (hpR1:pR≤1),p₀≤pH→
    ∀(q:U→Γ→ℝ) (hq:∀u z,0≤q u z) (hQ:∀u,∑z,q u z≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑z,q u z)) (j:Color),(∀u,s u j=pH)→
    let hpR0:0≤pR:=hp₀.le.trans hpR;
    1-χ≤(FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>pR) (fun _=>hpR0) (fun _=>hpR1) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀i≤L,EndpointPhysicalPotentialEvent (P.comap (f i)) (F.comap (f i)) (A i) (B i) (A i)ᶜ
        (π i) d j (weight i) pR pH t (ordinaryRawRestrictPair (f i) (g i) σ)):=by
  obtain ⟨N,hN⟩:=endpoint_physical_parent_potential_event K ω p₀ t hK hω hp₀ ht d 2 hd
  obtain ⟨M,hM⟩:=exists_nat_gt (2/((1-ε)*χ))
  let M₀:=max N (max M 2)
  have hM0:1≤M₀:=by dsimp [M₀];omega
  have hM0pos:(0:ℝ)<M₀:=by exact_mod_cast (show 0<M₀ by omega)
  have hMχ:2/((1-ε)*(M₀:ℝ))≤χ:=by
    have hden:0<(1-ε)*χ:=mul_pos (by linarith) hχ
    have hle:(M:ℝ)≤M₀:=by exact_mod_cast (show M≤M₀ by dsimp [M₀];omega)
    have hbig:2/((1-ε)*χ)≤(M₀:ℝ):=hM.le.trans hle
    have hh:2≤((1-ε)*χ)*(M₀:ℝ):=by simpa only [mul_comm] using (div_le_iff₀ hden).mp hbig
    apply (div_le_iff₀ (mul_pos (by linarith) hM0pos)).mpr
    nlinarith only [hh]
  refine ⟨M₀,hM0,?_⟩
  intro V U Γ Color W Z _ _ _ _ _ _ _ _ _ _ P F f g π A B L hn hstep hV hU hB hdeg hF hshort
  have hex:∀i,i≤L→∃weight:W i→Sym2 (W i⊕Z i)→ℝ,
      EndpointPhysicalParentWeights (P.comap (f i)) (A i) (A i)ᶜ weight ∧
      ∀(pR pH:ℝ) (hpR:p₀≤pR) (hpR1:pR≤1),p₀≤pH→
      ∀(q:U→Γ→ℝ) (hq:∀u z,0≤q u z) (hQ:∀u,∑z,q u z≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑z,q u z)) (j:Color),(∀u,s u j=pH)→
      1-2/((A i).card:ℝ)^2≤
        (FiniteLaw.pi (rawWheelLaw (V:=W i) (fun _=>pR) (fun _=>hp₀.le.trans hpR) (fun _=>hpR1) d hd
          (fun z=>q (g i z)) (fun z=>hq (g i z)) (fun z=>hQ (g i z))
          (fun z=>s (g i z)) (fun z=>hs (g i z)) (fun z=>hS (g i z)))).probability
            (EndpointPhysicalPotentialEvent (P.comap (f i)) (F.comap (f i)) (A i) (B i) (A i)ᶜ (π i) d j weight pR pH t):=by
    intro i hi
    obtain ⟨w,hw,hprob⟩:=hN (W i) (Z i) Γ Color (P.comap (f i)) (A i) (A i)ᶜ (by dsimp [M₀] at hn;have hh:=hn i hi;omega) (hdeg i hi)
    refine ⟨w,hw,?_⟩
    intro pR pH hpR hpR1 hpH q hq hQ s hs hS j hj
    exact hprob (F.comap (f i)) (π i) (B i) (hV i hi) (hU i hi) (hB i hi) (hF i hi) (hshort i hi)
      pR pH hpR hpR1 hpH (fun z=>q (g i z)) (fun z=>hq (g i z)) (fun z=>hQ (g i z))
      (fun z=>s (g i z)) (fun z=>hs (g i z)) (fun z=>hS (g i z)) j (fun z _=>hj (g i z))
  let weight:∀i,W i→Sym2 (W i⊕Z i)→ℝ:=fun i=>if hi:i≤L then Classical.choose (hex i hi) else fun _ _=>0
  refine ⟨weight,?_,?_⟩
  · intro i hi
    simpa only [weight,dif_pos hi] using (Classical.choose_spec (hex i hi)).1
  · intro pR pH hpR hpR1 hpH q hq hQ s hs hS j hj hpR0
    let μ:FiniteLaw (RawWheelOutcome V U Γ Color):=
      FiniteLaw.pi (rawWheelLaw (fun _=>pR) (fun _=>hpR0) (fun _=>hpR1) d hd q hq hQ s hs hS)
    let Good:=fun i (σ:RawWheelOutcome V U Γ Color)=>
      EndpointPhysicalPotentialEvent (P.comap (f i)) (F.comap (f i)) (A i) (B i) (A i)ᶜ (π i) d j (weight i) pR pH t
        (ordinaryRawRestrictPair (f i) (g i) σ)
    have hpos:∀i≤L,0<((A i).card:ℝ):=by
      intro i hi
      exact_mod_cast (show 0<(A i).card by have hh:=hn i hi;omega)
    have hlast:(M₀:ℝ)≤((A L).card:ℝ):=by exact_mod_cast (hn L (by omega))
    have hprob:∀i≤L,1-1/((A i).card:ℝ)≤μ.probability (Good i):=by
      intro i hi
      let Local:=EndpointPhysicalPotentialEvent (Γ:=Γ) (Color:=Color) (P.comap (f i)) (F.comap (f i)) (A i) (B i) (A i)ᶜ (π i) d j (weight i) pR pH t
      have hlaw:=ordinary_raw_pair_restriction_probability (f i) (f i).injective (g i) (g i).injective
        pR hpR0 hpR1 d hd q hq hQ s hs hS Local
      have hlocal:1-2/((A i).card:ℝ)^2≤(FiniteLaw.pi (rawWheelLaw (V:=W i) (fun _=>pR)
        (fun _=>hpR0) (fun _=>hpR1) d hd (fun z=>q (g i z)) (fun z=>hq (g i z)) (fun z=>hQ (g i z))
        (fun z=>s (g i z)) (fun z=>hs (g i z)) (fun z=>hS (g i z)))).probability Local:=by
        have hh:=(Classical.choose_spec (hex i hi)).2 pR pH hpR hpR1 hpH q hq hQ s hs hS j hj
        have hwEq:weight i=Classical.choose (hex i hi):=by simp only [weight,dif_pos hi]
        dsimp only [Local]
        rw [hwEq]
        convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
      have hAi:2≤((A i).card:ℝ):=by exact_mod_cast (show 2≤(A i).card by have hh:=hn i hi;dsimp [M₀] at hh;omega)
      have hinv:2/((A i).card:ℝ)^2≤1/((A i).card:ℝ):=by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith only [hAi]
      change 1-1/((A i).card:ℝ)≤μ.probability (fun σ=>Local (ordinaryRawRestrictPair (f i) (g i) σ))
      rw [hlaw]
      linarith only [hinv,hlocal]
    have hcommon:=vortex_fixed_domain_common_event μ ε (M₀:ℝ) hε hε1 hM0pos
      (fun i=>(A i).card) L hpos hstep hlast Good hprob
    have hhalf:1/((1-ε)*(M₀:ℝ))≤χ:=by
      have hh:0≤1/((1-ε)*(M₀:ℝ)):=by positivity
      have htwo:2/((1-ε)*(M₀:ℝ))=2*(1/((1-ε)*(M₀:ℝ))):=by ring
      linarith only [hMχ,hh,htwo]
    exact le_trans (by linarith only [hhalf]) hcommon
end Oberwolfach
