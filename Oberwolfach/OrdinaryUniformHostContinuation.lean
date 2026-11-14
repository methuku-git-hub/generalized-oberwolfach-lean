module

public import Oberwolfach.OrdinaryCombinedHostEventNamed

@[expose] public section
/-! Package the full-host continuation so its weights are fixed before
class-specific densities and probabilities are chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinaryUniformHostContinuation {V:Type} [Fintype V] [LinearOrder V]
    (m d k:ℕ) (hm:3≤m) (hd:2≤d) (P:SimpleGraph V)
    (θ α pstar ω βP ηP row ηH L βH c B ε:ℝ) (hpstar:0<pstar)
    (weight:OrdinaryCycle P (m+1)→ℝ):Prop :=
    ∀ (U Γ Color:Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U],
      ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ (F:SimpleGraph V) (π:Equiv.Perm V),
      (∀ v,(F.degree v:ℝ)≤L) → permutationConflictGraph π (3*d)≤F →
      (∀ x l,0<l→l<2*d+1→(π^l) x≠x) →
    ∀ pR pH D₀:ℝ,∀ hRlo:pstar≤pR,∀ hRhi:pR≤1,pstar≤pH→pH≤1→
      (Fintype.card V:ℝ)/2≤D₀→
      (∀ v,|(P.degree v:ℝ)-D₀|≤ε*Fintype.card V) → pR*D₀=2*(Fintype.card U:ℝ)*pH →
    ∀ (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j ≤ intervalUncoveredProbability d (∑ g,q u g))
      (j:Color),(∀ u,s u j=pH) →
    let μ:=FiniteLaw.pi (rawWheelLaw (fun _:Sym2 V=>pR) (fun _=>(hpstar.trans_le hRlo).le) (fun _=>hRhi) d hd q hq hQ s hs hS)
    1-(1/(Fintype.card V:ℝ)+3/(Fintype.card V:ℝ)^2)≤
      μ.probability (ordinaryCombinedHostEvent m d k hm P F π θ α pstar βP ηP row ηH βH c B pR pH weight s j)
end Oberwolfach
