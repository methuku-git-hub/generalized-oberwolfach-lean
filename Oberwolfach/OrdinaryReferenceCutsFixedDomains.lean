module

public import Oberwolfach.OrdinaryTriangleReferenceJoint
public import Oberwolfach.OrdinaryRawPairCoinRestriction
public import Oberwolfach.VortexCommonEvents

@[expose] public section
/-! The original normalized rim and spoke cuts hold simultaneously on every
fixed shrinking domain with the same raw sample and orientation coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reference_cuts_fixed_domains
    (α pstar ω:ℝ) (hα:0<α) (hα1:α≤1/2) (hp:0<pstar) (hp1:pstar≤1) (hω:0<ω):
    ∃δ h:ℝ,0<δ ∧ δ<1/4 ∧ 0<h ∧ ∀(η χ Lconf:ℝ),0<η→η<1→0<χ→0≤Lconf→
    ∀d:ℕ,∀hd:2≤d,∃M₀:ℕ,1≤M₀ ∧
    ∀(V U Γ Color:Type) (W Z:ℕ→Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
      [∀i,Fintype (W i)] [∀i,Fintype (Z i)] [∀i,LinearOrder (W i)] [∀i,DecidableEq (Z i)],
    ∀(P F:SimpleGraph V) (f:∀i,W i↪V) (g:∀i,Z i↪U) (π:∀i,Equiv.Perm (W i)) (A:∀i,Finset (W i)) (L:ℕ),
      (∀i≤L,M₀≤(A i).card)→(∀i<L,((A (i+1)).card:ℝ)≤η*(A i).card)→
      (∀i≤L,ω*Fintype.card (W i)≤(Fintype.card (Z i):ℝ) ∧ Fintype.card (Z i)≤Fintype.card (W i))→
      (∀i≤L,∀v,(1/2+α)*Fintype.card (W i)≤((P.comap (f i)).degree v:ℝ))→
      (∀i≤L,∀v,((F.comap (f i)).degree v:ℝ)≤Lconf)→
      (∀i≤L,∀x l,0<l→l<2*d+1→((π i)^l) x≠x)→
    ∀pR pH:ℝ,∀hR:0≤pR,∀hR1:pR≤1,pstar≤pR→pstar≤pH→
    ∀(q:U→Γ→ℝ) (hq:∀u z,0≤q u z) (hQ:∀u,∑z,q u z≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑z,q u z)) (j:Color) (hj:∀u,s u j=pH),
    let μ:=FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>pR) (fun _=>hR) (fun _=>hR1) d hd q hq hQ s hs hS)
    let ν:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin);
    1-χ≤(μ.prod ν).probability (fun z=>∀i≤L,
      OrdinaryTriangleReferenceNormalizedCuts (P.comap (f i)) (F.comap (f i)) (π i) d j δ h
        (ordinaryRawRestrictPair (f i) (g i) z.1) (fun e=>z.2 (Sym2.map (f i) e))) :=by
  obtain ⟨δ,h,hδ,hδ1,hh,hbase⟩:=ordinary_reference_large_cuts α pstar ω hα hα1 hp hp1 hω
  refine ⟨δ,h,hδ,hδ1,hh,?_⟩
  intro η χ Lconf hη hη1 hχ hL d hd
  obtain ⟨N,hN⟩:=hbase Lconf hL d 1 hd
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
  intro V U Γ Color W Z _ _ _ _ _ _ _ _ _ _ P F f g π A L hn hstep hU hmin hF hshort pR pH hR hR1 hRlo hH q hq hQ s hs hS j hj μ ν
  let Good:=fun i (z:RawWheelOutcome V U Γ Color×(Sym2 V→Bool))=>
    OrdinaryTriangleReferenceNormalizedCuts (P.comap (f i)) (F.comap (f i)) (π i) d j δ h
      (ordinaryRawRestrictPair (f i) (g i) z.1) (fun e=>z.2 (Sym2.map (f i) e))
  have hpos:∀i≤L,0<((A i).card:ℝ):=by
    intro i hi
    exact_mod_cast (show 0<(A i).card by have hh:=hn i hi;omega)
  have hlast:(M₀:ℝ)≤((A L).card:ℝ):=by exact_mod_cast (hn L (by omega))
  have hprob:∀i≤L,1-1/((A i).card:ℝ)≤(μ.prod ν).probability (Good i):=by
    intro i hi
    let Local:RawWheelOutcome (W i) (Z i) Γ Color×(Sym2 (W i)→Bool)→Prop:=fun z=>
      OrdinaryTriangleReferenceNormalizedCuts (P.comap (f i)) (F.comap (f i)) (π i) d j δ h z.1 z.2
    have hlaw:=ordinary_raw_pair_coin_restriction_probability (f i) (g i) pR hR hR1 d hd q hq hQ s hs hS Local
    have hsize:N≤Fintype.card (W i):=by
      have hh:=hn i hi
      have hc:=Finset.card_le_univ (A i)
      dsimp [M₀] at hh
      omega
    have hW:0<Fintype.card (W i):=by have hh:=hn i hi;have hc:=Finset.card_le_univ (A i);omega
    have hUpos:0<Fintype.card (Z i):=by
      have hw:(0:ℝ)<Fintype.card (W i):=by exact_mod_cast hW
      have hh:0<(Fintype.card (Z i):ℝ):=(mul_pos hω hw).trans_le (hU i hi).1
      exact_mod_cast hh
    have hlocal:=hN (W i) (Z i) Γ Color hsize (hU i hi).1 (hU i hi).2 (P.comap (f i)) (F.comap (f i))
      (hmin i hi) (hF i hi) (π i) (hshort i hi) pR pH hR hR1 hRlo hH
      (fun z=>q (g i z)) (fun z=>hq (g i z)) (fun z=>hQ (g i z))
      (fun z=>s (g i z)) (fun z=>hs (g i z)) (fun z=>hS (g i z)) j (fun z=>hj (g i z))
    have hlocal':1-1/(Fintype.card (W i):ℝ)≤
      ((FiniteLaw.pi (rawWheelLaw (V:=W i) (fun _=>pR) (fun _=>hR) (fun _=>hR1) d hd
        (fun z=>q (g i z)) (fun z=>hq (g i z)) (fun z=>hQ (g i z))
        (fun z=>s (g i z)) (fun z=>hs (g i z)) (fun z=>hS (g i z)))).prod
        (FiniteLaw.pi (fun _:Sym2 (W i)=>FiniteLaw.fairCoin))).probability Local:=by
      simp only [pow_one] at hlocal
      apply hlocal.trans
      apply finiteLaw_probability_mono
      intro z hz
      apply ordinary_reference_matrix_cuts_normalized (rawWheelGraph (P.comap (f i)) z.1) (F.comap (f i))
        (rawWheelSpokes (π i) d z.1 j) z.2 δ (2*h) hW hUpos
      · intro S T hST
        have he:relationMultiplicity (rawWheelSpokes (π i) d z.1 j)=
            (fun v u=>if rawWheelSpokes (π i) d z.1 j v u then 1 else 0):=by
          funext v u
          simp only [relationMultiplicity]
        rw [he]
        exact hz.1 S T hST
      · exact hz.2
    have hc:((A i).card:ℝ)≤Fintype.card (W i):=by exact_mod_cast Finset.card_le_univ (A i)
    have hinv:1/(Fintype.card (W i):ℝ)≤1/((A i).card:ℝ):=one_div_le_one_div_of_le (hpos i hi) hc
    change 1-1/((A i).card:ℝ)≤(μ.prod ν).probability (fun z=>Local (ordinaryRawRestrictPair (f i) (g i) z.1,fun e=>z.2 (Sym2.map (f i) e)))
    rw [hlaw]
    linarith only [hinv,hlocal']
  have hcommon:=vortex_fixed_domain_common_event (μ.prod ν) η (M₀:ℝ) hη hη1 hM0pos
    (fun i=>(A i).card) L hpos hstep hlast Good hprob
  exact le_trans (by linarith only [hMχ]) hcommon
end Oberwolfach
