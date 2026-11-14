module

public import Oberwolfach.OrderedOrdinarySeedHubTarget

@[expose] public section
/-! Convert the sampled hub total to the unreserved component-frequency
centre, keeping the concentration and positional errors explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordered_ordinary_sampled_seed_hub_frequency
    (P:SimpleGraph V) (π:Equiv.Perm V) (p k:ℝ) (hp:0<p) (hk:0≤k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j ≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (m:ℕ) (hm:2≤m) (g:Γ) (j:Color) (D τ:ℝ) (hD:0<D) (hτ:0≤τ) (hspos:∀u,0<s u j)
    (η:U→ℝ) (hη:∀u,0≤η u) (weight:(Fin (m+1)→V)→ℝ)
    (hsupport:∀W:OrderedOrdinaryWheel (U:=U) π (3*d) (m+1),weight W.1.val≠0→
      ∀i:Fin (m+1),P.Adj (W.1.val i) (W.1.val (cycleNext i)))
    (hpos:∀v:V,∀i:Fin (m+1),(1-τ)*D≤(∑C:{C:Fin (m+1)→V // PermutationSeparated π (3*d) C},if C.val i=v then weight C.val else 0) ∧
      (∑C:{C:Fin (m+1)→V // PermutationSeparated π (3*d) C},if C.val i=v then weight C.val else 0)≤(1+τ)*D)
    (hub:U) (θ f t:ℝ) (hfreq:η hub*s hub j=(1-θ)*f)
    (σ:RawMarkedOutcome V U Γ Color):
    let seed:=fun W:OrderedOrdinaryWheel (U:=U) π (3*d) (m+1)=>η W.2*weight W.1.val/
      (((m+1:ℕ):ℝ)*D*p^(m+1)*(s W.2 j)^m)
    let mean:=(FiniteLaw.pi (rawMarkedWheelLaw p k hp.le hk hsum d hd q hq hQ s hs hS)).expectation
      (orderedOrdinarySampledHubTotal P π d m seed g j hub)
    let target:ℝ:=(1-θ)*f*(Fintype.card V:ℝ)/((m+1:ℕ):ℝ);
    |orderedOrdinarySampledHubTotal P π d m seed g j hub σ-mean|<t →
    |orderedOrdinarySampledHubTotal P π d m seed g j hub σ-target|<t+τ*target :=by
  intro seed mean target hsample
  have hmean:=ordered_ordinary_seed_hub_target P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort m hm g j D τ hD hspos η hη weight hsupport hpos hub
  change (1-τ)*(η hub*s hub j)*(Fintype.card V:ℝ)/((m+1:ℕ):ℝ)≤mean ∧
    mean≤(1+τ)*(η hub*s hub j)*(Fintype.card V:ℝ)/((m+1:ℕ):ℝ) at hmean
  rw [hfreq] at hmean
  have heqlo:(1-τ)*((1-θ)*f)*(Fintype.card V:ℝ)/((m+1:ℕ):ℝ)=(1-τ)*target:=by dsimp [target];ring
  have heqhi:(1+τ)*((1-θ)*f)*(Fintype.card V:ℝ)/((m+1:ℕ):ℝ)=(1+τ)*target:=by dsimp [target];ring
  rw [heqlo,heqhi] at hmean
  have hlo:=hmean.1
  have hhi:=hmean.2
  have hh:=abs_lt.mp hsample
  apply abs_lt.mpr
  constructor <;> nlinarith [hh.1,hh.2]
end Oberwolfach
