module

public import Oberwolfach.OrdinaryReferenceCutsFixedDomains

@[expose] public section
/-! Package the common normalized rim and spoke cuts on fixed domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryReferenceCutsDomainSelector
    (d M:ℕ) (hd:2≤d) (α pstar ω δ h η χ Lconf:ℝ):Prop :=
    ∀(V U Γ Color:Type) (W Z:ℕ→Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
      [∀i,Fintype (W i)] [∀i,Fintype (Z i)] [∀i,LinearOrder (W i)] [∀i,DecidableEq (Z i)],
    ∀(P F:SimpleGraph V) (f:∀i,W i↪V) (g:∀i,Z i↪U) (π:∀i,Equiv.Perm (W i)) (A:∀i,Finset (W i)) (L:ℕ),
      (∀i≤L,M≤(A i).card)→(∀i<L,((A (i+1)).card:ℝ)≤η*(A i).card)→
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
        (ordinaryRawRestrictPair (f i) (g i) z.1) (fun e=>z.2 (Sym2.map (f i) e)))
end Oberwolfach
