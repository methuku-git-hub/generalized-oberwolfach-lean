module

public import Oberwolfach.OrdinaryCombinedTriangleFixedDomains

@[expose] public section
/-! Package the fixed-domain triangle selector so weight selection and the
subsequent original-vortex instantiation can be checked in separate modules. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleFixedDomainSelector
    (k d M:ℕ) (hd:2≤d) (θ α pstar ω βP ηP ηH βH c B ε η χ Lconf:ℝ) (hpstar:0<pstar):Prop :=
    ∀(V U Γ Color:Type) (W Z:ℕ→Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
      [∀i,Fintype (W i)] [∀i,Fintype (Z i)] [∀i,LinearOrder (W i)] [∀i,DecidableEq (Z i)],
    ∀(P F:SimpleGraph V) (f:∀i,W i↪V) (g:∀i,Z i↪U) (π:∀i,Equiv.Perm (W i))
      (A:∀i,Finset (W i)) (L:ℕ),
      (∀i≤L,M≤(A i).card)→(∀i<L,((A (i+1)).card:ℝ)≤η*(A i).card)→
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
      θ α pstar βP ηP ηH βH c B pR pH (weight i) j (ordinaryRawRestrictPair (f i) (g i) raw))
end Oberwolfach
