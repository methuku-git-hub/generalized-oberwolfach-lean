module

public import Oberwolfach.OrderedOrdinarySpokeTarget

@[expose] public section
/-! The sampled load at a spoke has the actual supplied hub coefficient as
its centre, with both the concentration error and positional error visible. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_sampled_spoke_target
    (P:SimpleGraph V) (π:Equiv.Perm V) (p k:ℝ) (hp:0<p) (hk:0≤k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (r:ℕ) (hr:3≤r) (g:Γ) (j:Color) (D τ:ℝ) (hD:0<D) (hspos:∀ u,0<s u j)
    (η:U→ℝ) (hη:∀ u,0≤η u) (weight:(Fin r→V)→ℝ)
    (hsupport:∀ W:OrderedOrdinaryWheel (U:=U) π (3*d) r,weight W.1.val≠0→
      ∀ i:Fin r,P.Adj (W.1.val i) (W.1.val (cycleNext i)))
    (v:V) (u:U)
    (hpos:∀ i:Fin r,(1-τ)*D≤(∑ C:{C:Fin r→V // PermutationSeparated π (3*d) C},if C.val i=v then weight C.val else 0) ∧
      (∑ C:{C:Fin r→V // PermutationSeparated π (3*d) C},if C.val i=v then weight C.val else 0)≤(1+τ)*D)
    (σ:∀ e:RawWheelCoordinate V U,RawMarkedCoordinateState Γ Color e) (t:ℝ) :
    let seed:=fun W:OrderedOrdinaryWheel (U:=U) π (3*d) r=>η W.2*weight W.1.val/((r:ℝ)*D*p^r*(s W.2 j)^(r-1))
    let load:=resourcePatternLoad orderedOrdinaryResources seed (fun _ _=>true) (Sum.inr (v,u)) (orderedOrdinaryResourceState P π d g j σ)
    let rootMean:=∑ W,(if Sum.inr (v,u)∈orderedOrdinaryResources W then seed W else 0)*
      ∏ a∈orderedOrdinaryResources W\{Sum.inr (v,u)},rawMarkedWheelMarginal P π d p k q s g j (orderedOrdinaryResourceEmbedding a)
    |load-rootMean|<t → |load-η u|<t+τ*η u := by
  intro seed load rootMean hload
  have hmean:=orderedOrdinary_seed_spoke_target P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort r hr g j D τ hD hspos η hη weight hsupport v u hpos
  have heq:=orderedOrdinary_potential_expectation P π p k hp.le hk hsum d hd q hq hQ s hs hS hnoshort r hr seed g j (Sum.inr (v,u))
  change _ = rootMean at heq
  dsimp only at hmean
  rw [heq] at hmean
  have hh:=abs_lt.mp hload
  apply abs_lt.mpr
  constructor <;> nlinarith [hmean.1,hmean.2,hh.1,hh.2]
end Oberwolfach
