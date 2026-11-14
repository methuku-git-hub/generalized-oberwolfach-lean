module

public import Oberwolfach.RawOrdinarySpokeCuts
public import Oberwolfach.OrdinaryRawPairRestriction
public import Oberwolfach.BipartiteLargeCutEmbedding
public import Oberwolfach.VortexCommonEvents

@[expose] public section
/-! One raw sample has the normalized spoke cuts simultaneously on every
fixed geometrically shrinking domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_spoke_cuts_fixed_domains
    (pstar ω:ℝ) (hp:0<pstar) (hp1:pstar≤1) (hω:0<ω)
    (η χ:ℝ) (hη:0<η) (hη1:η<1) (hχ:0<χ) (d:ℕ) (hd:2≤d):
    ∃M₀:ℕ,1≤M₀ ∧
    ∀(V U Γ Color:Type) (W Z:ℕ→Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
      [∀i,Fintype (W i)] [∀i,Fintype (Z i)] [∀i,LinearOrder (W i)] [∀i,DecidableEq (Z i)],
    ∀(f:∀i,W i↪V) (g:∀i,Z i↪U) (π:∀i,Equiv.Perm (W i)) (A:∀i,Finset (W i)) (L:ℕ),
      (∀i≤L,M₀≤(A i).card)→(∀i<L,((A (i+1)).card:ℝ)≤η*(A i).card)→
      (∀i≤L,ω*Fintype.card (W i)≤(Fintype.card (Z i):ℝ) ∧ Fintype.card (Z i)≤Fintype.card (W i))→
      (∀i≤L,∀x l,0<l→l<2*d+1→((π i)^l) x≠x)→
    ∀pR pH:ℝ,∀hR:0≤pR,∀hR1:pR≤1,pstar≤pH→
    ∀(q:U→Γ→ℝ) (hq:∀u z,0≤q u z) (hQ:∀u,∑z,q u z≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑z,q u z)) (j:Color) (hj:∀u,s u j=pH),
    let μ:=FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>pR) (fun _=>hR) (fun _=>hR1) d hd q hq hQ s hs hS);
    1-χ≤μ.probability (fun raw=>∀i≤L,
      BipartiteLargeCut (relationMultiplicity (rawWheelSpokes (π i) d (ordinaryRawRestrictPair (f i) (g i) raw) j))
        (pstar/16) (pstar/8)) :=by
  obtain ⟨N,hN⟩:=rawWheelSpokeCuts_uniform_probability pstar ω hp hp1 hω d 1 hd
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
  intro V U Γ Color W Z _ _ _ _ _ _ _ _ _ _ f g π A L hn hstep hU hshort pR pH hR hR1 hH q hq hQ s hs hS j hj μ
  let Good:=fun i (raw:RawWheelOutcome V U Γ Color)=>
    BipartiteLargeCut (relationMultiplicity (rawWheelSpokes (π i) d (ordinaryRawRestrictPair (f i) (g i) raw) j)) (pstar/16) (pstar/8)
  have hpos:∀i≤L,0<((A i).card:ℝ):=by
    intro i hi
    exact_mod_cast (show 0<(A i).card by have hh:=hn i hi;omega)
  have hlast:(M₀:ℝ)≤((A L).card:ℝ):=by exact_mod_cast (hn L (by omega))
  have hprob:∀i≤L,1-1/((A i).card:ℝ)≤μ.probability (Good i):=by
    intro i hi
    let Local:RawWheelOutcome (W i) (Z i) Γ Color→Prop:=fun raw=>
      BipartiteLargeCut (relationMultiplicity (rawWheelSpokes (π i) d raw j)) (pstar/16) (pstar/8)
    have hlaw:=ordinary_raw_pair_restriction_probability (f i) (f i).injective (g i) (g i).injective
      pR hR hR1 d hd q hq hQ s hs hS Local
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
    have hlocal:=hN (W i) (Z i) Γ Color hsize (hU i hi).1 (hU i hi).2 (π i)
      (fun _=>pR) (fun _=>hR) (fun _=>hR1)
      (fun z=>q (g i z)) (fun z=>hq (g i z)) (fun z=>hQ (g i z))
      (fun z=>s (g i z)) (fun z=>hs (g i z)) (fun z=>hS (g i z)) j (hshort i hi) pH hH (fun z=>hj (g i z))
    have hlocal':1-1/(Fintype.card (W i):ℝ)≤
        (FiniteLaw.pi (rawWheelLaw (V:=W i) (fun _=>pR) (fun _=>hR) (fun _=>hR1) d hd
          (fun z=>q (g i z)) (fun z=>hq (g i z)) (fun z=>hQ (g i z))
          (fun z=>s (g i z)) (fun z=>hs (g i z)) (fun z=>hS (g i z)))).probability Local:=by
      simp only [pow_one] at hlocal
      apply hlocal.trans
      apply finiteLaw_probability_mono
      intro raw hraw S T hST
      rw [bipartiteLargeCut_sum_restrict,bipartite_normalized_cut_scale hW hUpos]
      have hh:=hraw S T (by convert hST using 1 <;> ring)
      have he:relationMultiplicity (rawWheelSpokes (π i) d raw j)=
          (fun v u=>if rawWheelSpokes (π i) d raw j v u then 1 else 0):=by
        funext v u
        simp only [relationMultiplicity]
      rw [he]
      exact hh
    have hc:((A i).card:ℝ)≤Fintype.card (W i):=by exact_mod_cast Finset.card_le_univ (A i)
    have hinv:1/(Fintype.card (W i):ℝ)≤1/((A i).card:ℝ):=one_div_le_one_div_of_le (hpos i hi) hc
    change 1-1/((A i).card:ℝ)≤μ.probability (fun raw=>Local (ordinaryRawRestrictPair (f i) (g i) raw))
    rw [hlaw]
    linarith only [hinv,hlocal']
  have hcommon:=vortex_fixed_domain_common_event μ η (M₀:ℝ) hη hη1 hM0pos
    (fun i=>(A i).card) L hpos hstep hlast Good hprob
  exact le_trans (by linarith only [hMχ]) hcommon
end Oberwolfach
