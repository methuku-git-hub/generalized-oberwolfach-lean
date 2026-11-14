module

public import Oberwolfach.OrdinaryShiftedIntervalSpokeTarget
public import Oberwolfach.OrdinaryShiftedMarkedPotentialSampling

@[expose] public section
/-! Pointwise conversion of an all-root concentration event to the marked
spoke target; no resampling or new density is introduced. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_shifted_interval_spoke_concentration_target
    (P:SimpleGraph V) (π:Equiv.Perm V)
    (p k:ℝ) (hp:0<p) (hk:0≤k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (m:ℕ) (hm:2≤m) (g:Γ) (j:Color) (D τ A B t:ℝ) (hD:0<D)
    (hspos:∀ u,0<s u j)
    (weight:(Fin (m+1)→V)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (σ:RawMarkedOutcome V U Γ Color):
    let H₀:=fun (_:V) (_:U)=>True
    let Hₖ:=fun (_:V) (_:U)=>True
    let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ=>
      weight W.1.val/(D*p^(m+1)*(s W.2.val j)^m);
    (∀ root,|typedMarkedPotentialLoad seed (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) root-
        ∑ W,(if root∈typedMarkedOccurrenceResources W then seed W else 0)*
          ∏ a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p p q s g j a|<t)→
    ∀ x u,q u g≠0→
      |typedMarkedPotentialLoad seed (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) (Sum.inr (true,x,u))-1|<t+τ :=by
  intro H₀ Hₖ seed hconc x u hqu
  let root:((V×V)⊕(V×V))⊕(Bool×V×U):=Sum.inr (true,x,u)
  let mean:=(FiniteLaw.pi (rawMarkedWheelLaw p k hp.le hk hsum d hd q hq hQ s hs hS)).expectation
    (fun ω=>typedMarkedPotentialLoad seed (ordinaryShiftedPairRims P π d ω) (rawMarkedPairSpokes π d ω g j) root)
  have hmean:=ordinary_shifted_potential_expectation P π p k hp.le hk hsum d hd q hq hQ s hs hS
    hnoshort m hm H₀ Hₖ seed g j root
  have hc:=hconc root
  rw [←hmean] at hc
  have htarg:=ordinary_shifted_interval_spoke_target P π p k hp hk hsum d hd q hq hQ s hs hS
    hnoshort m hm g j D τ A B hD hspos weight hw x u hqu
  change 1-τ≤mean ∧ mean≤1 at htarg
  have hdiff:|mean-1|≤τ:=abs_le.mpr ⟨by linarith [htarg.1],by linarith [htarg.2]⟩
  calc
    _ ≤ |typedMarkedPotentialLoad seed (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) root-mean|+|mean-1|:=abs_sub_le _ _ _
    _ < t+τ:=add_lt_add_of_lt_of_le hc hdiff
end Oberwolfach
