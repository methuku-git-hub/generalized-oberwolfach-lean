module

public import Oberwolfach.OrdinaryTriangleEventNamedAtLeast
public import Oberwolfach.OrdinaryRawPairRestriction
public import Oberwolfach.VortexCommonEvents
public import Oberwolfach.OrdinaryTriangleFailureArithmetic

@[expose] public section
/-! Choose fixed cycle weights before sampling and intersect the combined
triangle events over a geometrically shrinking family of fixed domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 35000000
set_option synthInstance.maxSize 32768
set_option maxRecDepth 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_combined_triangle_fixed_domains
    (kmin d:ℕ) (hd:2≤d) (θ α pstar ω βP ηP Lconf:ℝ)
    (hθ:cycleThreshold 3≤θ) (hα:0<α) (hα1:α≤1) (hθ1:θ+α/2≤1)
    (hpstar:0<pstar) (hpstar1:pstar≤1) (hω:0<ω)
    (hβP:0<βP) (hβmax:βP≤2*(min (α/2) (1/4))*pstar^4*pstar^4)
    (hβhub:βP≤ω*pstar^9/4) (hηP:0<ηP) (hL:0≤Lconf):
    ∃(k:ℕ) (βH c B:ℝ),5≤k ∧ kmin≤k ∧ 0<βH ∧ 0<c ∧ 0<B ∧
    ∀ηH η χ:ℝ,0<ηH→0<η→η<1→0<χ→
    ∃ ε:ℝ,0<ε ∧ ∃M₀:ℕ,1≤M₀ ∧
    ∀(V U Γ Color:Type) (W Z:ℕ→Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
      [∀i,Fintype (W i)] [∀i,Fintype (Z i)] [∀i,LinearOrder (W i)] [∀i,DecidableEq (Z i)],
    ∀(P F:SimpleGraph V) (f:∀i,W i↪V) (g:∀i,Z i↪U) (π:∀i,Equiv.Perm (W i))
      (A:∀i,Finset (W i)) (L:ℕ),
      (∀i≤L,M₀≤(A i).card)→(∀i<L,((A (i+1)).card:ℝ)≤η*(A i).card)→
      (∀i≤L,∀v,(θ+α)*Fintype.card (W i)≤((P.comap (f i)).degree v:ℝ))→
    ∃weight:∀i,OrdinaryCycle (P.comap (f i)) 3→ℝ,
      (∀i≤L,(∀C,c/(Fintype.card (W i):ℝ)^(3-2)≤weight i C ∧ weight i C≤B/(Fintype.card (W i):ℝ)^(3-2)) ∧
        (∀x y,(∑C,if C.val.val.Adj x y then weight i C else 0)=if (P.comap (f i)).Adj x y then 1 else 0)) ∧
    ∀(pR pH:ℝ) (D:ℕ→ℝ),
      (∀i≤L,ω*Fintype.card (W i)≤(Fintype.card (Z i):ℝ) ∧ Fintype.card (Z i)≤Fintype.card (W i))→
      (∀i≤L,∀v,((F.comap (f i)).degree v:ℝ)≤Lconf)→
      (∀i≤L,permutationConflictGraph (π i) (3*d)≤F.comap (f i))→
      (∀i≤L,∀x l,0<l→l<2*d+1→((π i)^l) x≠x)→
      (hRlo:pstar≤pR)→(hRhi:pR≤1)→pstar≤pH→pH≤1→
      (∀i≤L,(Fintype.card (W i):ℝ)/2≤D i)→
      (∀i≤L,∀v,|((P.comap (f i)).degree v:ℝ)-D i|≤ε*Fintype.card (W i))→
      (∀i≤L,pR*D i=2*(Fintype.card (Z i):ℝ)*pH)→
    ∀(q:U→Γ→ℝ) (hq:∀u z,0≤q u z) (hQ:∀u,∑z,q u z≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑z,q u z)) (j:Color) (hj:∀u,s u j=pH),
    let μ:=FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>pR) (fun _=>(hpstar.trans_le hRlo).le) (fun _=>hRhi) d hd q hq hQ s hs hS);
    1-χ≤μ.probability (fun raw=>∀i≤L,ordinaryCombinedTriangleEvent d k (P.comap (f i)) (F.comap (f i)) (π i)
      θ α pstar βP ηP ηH βH c B pR pH (weight i) j (ordinaryRawRestrictPair (f i) (g i) raw)) :=by
  obtain ⟨k,βH,c,B,hk,hkmin,hβH,hc,hB,hbase⟩:=ordinary_full_host_and_triangle_inputs_named_at_least
    kmin d hd θ α pstar ω βP ηP Lconf hθ hα hα1 hθ1 hpstar hpstar1 hω hβP hβmax hβhub hηP hL
  refine ⟨k,βH,c,B,hk,hkmin,hβH,hc,hB,?_⟩
  intro ηH η χ hηH hη hη1 hχ
  obtain ⟨ε,hε,N,hbase⟩:=hbase ηH hηH
  obtain ⟨M,hM⟩:=exists_nat_gt (4/((1-η)*χ))
  let M₀:=max N (max M 1)
  have hM0:1≤M₀:=by dsimp [M₀];omega
  have hM0pos:(0:ℝ)<M₀:=by exact_mod_cast (show 0<M₀ by omega)
  have hMχ:1/((1-η)*((M₀:ℝ)/4))≤χ:=by
    have hden:0<(1-η)*χ:=mul_pos (by linarith) hχ
    have hle:(M:ℝ)≤M₀:=by exact_mod_cast (show M≤M₀ by dsimp [M₀];omega)
    have hbig:4/((1-η)*χ)≤(M₀:ℝ):=hM.le.trans hle
    have hh:4≤((1-η)*χ)*(M₀:ℝ):=by simpa only [mul_comm] using (div_le_iff₀ hden).mp hbig
    apply (div_le_iff₀ (mul_pos (by linarith) (by positivity : (0:ℝ)<M₀/4))).mpr
    nlinarith only [hh]
  refine ⟨ε,hε,M₀,hM0,?_⟩
  intro V U Γ Color W Z _ _ _ _ _ _ _ _ _ _ P F f g π A L hn hstep hdegree
  have hsize:∀i≤L,N≤Fintype.card (W i):=by
    intro i hi
    have hh:=hn i hi
    have hc:=Finset.card_le_univ (A i)
    dsimp [M₀] at hh
    omega
  have hlocal:∀i≤L,∃weight:OrdinaryCycle (P.comap (f i)) 3→ℝ,
      (∀C,c/(Fintype.card (W i):ℝ)^(3-2)≤weight C ∧ weight C≤B/(Fintype.card (W i):ℝ)^(3-2)) ∧
      (∀x y,(∑C,if C.val.val.Adj x y then weight C else 0)=if (P.comap (f i)).Adj x y then 1 else 0) ∧
      ∀ (U' Γ' Color':Type) [Fintype U'] [Fintype Γ'] [Fintype Color'] [DecidableEq U'],
        ω*Fintype.card (W i)≤(Fintype.card U':ℝ) → Fintype.card U'≤Fintype.card (W i) →
      ∀ (F':SimpleGraph (W i)) (π':Equiv.Perm (W i)),
        (∀v,(F'.degree v:ℝ)≤Lconf) → permutationConflictGraph π' (3*d)≤F' →
        (∀x l,0<l→l<2*d+1→(π'^l) x≠x) →
      ∀ pR pH D₀:ℝ,∀ hRlo:pstar≤pR,∀ hRhi:pR≤1,pstar≤pH→pH≤1→
        (Fintype.card (W i):ℝ)/2≤D₀→(∀v,|((P.comap (f i)).degree v:ℝ)-D₀|≤ε*Fintype.card (W i))→
        pR*D₀=2*(Fintype.card U':ℝ)*pH→
      ∀(q:U'→Γ'→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
       (s:U'→Color'→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
       (j:Color'),(∀u,s u j=pH)→
       let μ:=FiniteLaw.pi (rawWheelLaw (fun _:Sym2 (W i)=>pR) (fun _=>(hpstar.trans_le hRlo).le) (fun _=>hRhi) d hd q hq hQ s hs hS)
       1-(1/(Fintype.card (W i):ℝ)+3/(Fintype.card (W i):ℝ)^2)≤
         μ.probability (ordinaryCombinedTriangleEvent d k (P.comap (f i)) F' π' θ α pstar βP ηP ηH βH c B pR pH weight j):=by
    intro i hi
    exact hbase (W i) (hsize i hi) (P.comap (f i)) (hdegree i hi)
  let weight:∀i,OrdinaryCycle (P.comap (f i)) 3→ℝ:=fun i=>if hi:i≤L then Classical.choose (hlocal i hi) else fun _=>0
  have hw:∀i≤L,(∀C,c/(Fintype.card (W i):ℝ)^(3-2)≤weight i C ∧ weight i C≤B/(Fintype.card (W i):ℝ)^(3-2)) ∧
      (∀x y,(∑C,if C.val.val.Adj x y then weight i C else 0)=if (P.comap (f i)).Adj x y then 1 else 0):=by
    intro i hi
    have hs:=Classical.choose_spec (hlocal i hi)
    constructor
    · simpa only [weight,dif_pos hi] using hs.1
    · simpa only [weight,dif_pos hi] using hs.2.1
  refine ⟨weight,hw,?_⟩
  intro pR pH D hU hF hconf hshort hRlo hRhi hHlo hHhi hDlo hreg hbal q hq hQ s hs hS j hj μ
  let Good:=fun i (raw:RawWheelOutcome V U Γ Color)=>ordinaryCombinedTriangleEvent d k (P.comap (f i)) (F.comap (f i)) (π i)
    θ α pstar βP ηP ηH βH c B pR pH (weight i) j (ordinaryRawRestrictPair (f i) (g i) raw)
  have hpos:∀i≤L,0<((A i).card:ℝ)/4:=by
    intro i hi
    have hh:0<((A i).card:ℝ):=by exact_mod_cast (show 0<(A i).card by have hh:=hn i hi;omega)
    positivity
  have hlast:(M₀:ℝ)/4≤((A L).card:ℝ)/4:=by
    have hh:(M₀:ℝ)≤(A L).card:=by exact_mod_cast (hn L (by omega))
    linarith
  have hstep':∀i<L,((A (i+1)).card:ℝ)/4≤η*(((A i).card:ℝ)/4):=by
    intro i hi
    have hh:=hstep i hi
    linarith
  have hprob:∀i≤L,1-1/(((A i).card:ℝ)/4)≤μ.probability (Good i):=by
    intro i hi
    let Local:RawWheelOutcome (W i) (Z i) Γ Color→Prop:=ordinaryCombinedTriangleEvent d k (P.comap (f i)) (F.comap (f i)) (π i)
      θ α pstar βP ηP ηH βH c B pR pH (weight i) j
    have hlaw:=ordinary_raw_pair_restriction_probability (f i) (f i).injective (g i) (g i).injective
      pR (hpstar.trans_le hRlo).le hRhi d hd q hq hQ s hs hS Local
    have hbasei:=(Classical.choose_spec (hlocal i hi)).2.2
    have hpi:=hbasei (Z i) Γ Color (hU i hi).1 (hU i hi).2 (F.comap (f i)) (π i)
      (hF i hi) (hconf i hi) (hshort i hi) pR pH (D i) hRlo hRhi hHlo hHhi (hDlo i hi) (hreg i hi) (hbal i hi)
      (fun z=>q (g i z)) (fun z=>hq (g i z)) (fun z=>hQ (g i z))
      (fun z=>s (g i z)) (fun z=>hs (g i z)) (fun z=>hS (g i z)) j (fun z=>hj (g i z))
    have hApos:0<((A i).card:ℝ):=by have hh:=hpos i hi;linarith
    have hAW:((A i).card:ℝ)≤Fintype.card (W i):=by exact_mod_cast Finset.card_le_univ (A i)
    have hWone:(1:ℝ)≤Fintype.card (W i):=by
      exact_mod_cast (show 1≤Fintype.card (W i) by have hh:=hn i hi;have hc:=Finset.card_le_univ (A i);omega)
    have hwp:weight i=Classical.choose (hlocal i hi):=by simp only [weight,dif_pos hi]
    change 1-1/(((A i).card:ℝ)/4)≤μ.probability (fun raw=>Local (ordinaryRawRestrictPair (f i) (g i) raw))
    rw [hlaw]
    have hpi':1-(1/(Fintype.card (W i):ℝ)+3/(Fintype.card (W i):ℝ)^2)≤
        (FiniteLaw.pi (rawWheelLaw (fun _:Sym2 (W i)=>pR) (fun _=>(hpstar.trans_le hRlo).le)
          (fun _=>hRhi) d hd (fun z=>q (g i z)) (fun z=>hq (g i z)) (fun z=>hQ (g i z))
          (fun z=>s (g i z)) (fun z=>hs (g i z)) (fun z=>hS (g i z)))).probability Local:=by
      change 1-(1/(Fintype.card (W i):ℝ)+3/(Fintype.card (W i):ℝ)^2)≤
        (FiniteLaw.pi (rawWheelLaw (fun _:Sym2 (W i)=>pR) (fun _=>(hpstar.trans_le hRlo).le)
          (fun _=>hRhi) d hd (fun z=>q (g i z)) (fun z=>hq (g i z)) (fun z=>hQ (g i z))
          (fun z=>s (g i z)) (fun z=>hs (g i z)) (fun z=>hS (g i z)))).probability
            (ordinaryCombinedTriangleEvent d k (P.comap (f i)) (F.comap (f i)) (π i)
              θ α pstar βP ηP ηH βH c B pR pH (weight i) j)
      rw [hwp]
      exact hpi
    exact (ordinary_triangle_failure_arithmetic (A i).card (Fintype.card (W i)) hApos hAW hWone).trans hpi'
  have hcommon:=vortex_fixed_domain_common_event μ η ((M₀:ℝ)/4) hη hη1 (by positivity)
    (fun i=>(A i).card/4) L hpos hstep' hlast Good hprob
  exact le_trans (by linarith only [hMχ]) hcommon
end Oberwolfach
