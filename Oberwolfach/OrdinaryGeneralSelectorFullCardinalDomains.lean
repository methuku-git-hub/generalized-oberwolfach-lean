module

public import Oberwolfach.OrdinaryGeneralSelectorFullDomains

@[expose] public section
/-! Specialize the general selector to full domains while its dependent
types remain abstract. This keeps vortex subtype elaboration separate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_selector_full_cardinal_domains
    (m k d M:ℕ) (hm:3≤m) (hd:2≤d) (θ α pstar ω βP ηP row ηH βH c B ε η χ Lconf:ℝ) (hpstar:0<pstar)
    (hselector:OrdinaryGeneralFixedDomainSelector m k d M hm hd θ α pstar ω βP ηP row ηH βH c B ε η χ Lconf hpstar)
    (V U Γ Color:Type) (W Z:ℕ→Type)
    [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
    [∀i,Fintype (W i)] [∀i,Fintype (Z i)] [∀i,LinearOrder (W i)] [∀i,DecidableEq (Z i)]
    (P F:SimpleGraph V) (f:∀i,W i↪V) (g:∀i,Z i↪U) (π:∀i,Equiv.Perm (W i)) (L:ℕ)
    (hsize:∀i≤L,M≤Fintype.card (W i))
    (hstep:∀i<L,(Fintype.card (W (i+1)):ℝ)≤η*Fintype.card (W i))
    (hdegree:∀i≤L,∀v,(θ+α)*Fintype.card (W i)≤((P.comap (f i)).degree v:ℝ)):
    ∃weight:∀i,OrdinaryCycle (P.comap (f i)) (m+1)→ℝ,
      (∀i≤L,(∀C,c/(Fintype.card (W i):ℝ)^((m+1)-2)≤weight i C ∧ weight i C≤B/(Fintype.card (W i):ℝ)^((m+1)-2)) ∧
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
    1-χ≤μ.probability (fun raw=>∀i≤L,ordinaryCombinedHostEvent m d k hm (P.comap (f i)) (F.comap (f i)) (π i)
      θ α pstar βP ηP row ηH βH c B pR pH (weight i) (fun z=>s (g i z)) j (ordinaryRawRestrictPair (f i) (g i) raw)) :=by
  apply ordinary_general_selector_full_domains m k d M hm hd θ α pstar ω βP ηP row ηH βH c B ε η χ Lconf hpstar
    hselector V U Γ Color W Z P F f g π L
  · simpa only [Finset.card_univ] using hsize
  · simpa only [Finset.card_univ] using hstep
  · exact hdegree
end Oberwolfach
