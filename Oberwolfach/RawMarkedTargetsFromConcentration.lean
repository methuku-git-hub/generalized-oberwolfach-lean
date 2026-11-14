module

public import Oberwolfach.RawMarkedVariableSpokeConcentrationTarget
public import Oberwolfach.RawMarkedOrdinaryArcConcentration
public import Oberwolfach.RawMarkedClosingArcConcentration
public import Oberwolfach.RawMarkedOrdinarySpokeConcentration

@[expose] public section
/-! A single all-root concentration event implies all four target estimates
for the same sample, the fixed weight, and its supplied density profile. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem raw_marked_all_targets_from_concentration
    (P:SimpleGraph V) (π:Equiv.Perm V)
    (p k:ℝ) (hp:0<p) (hk:0<k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (m:ℕ) (hm:2≤m) (g:Γ) (j:Color) (D τ A B t:ℝ) (hD:0<D)
    (hspos:∀u,0<s u j) (hbalance:∑u,q u g=D*k)
    (weight:(Fin (m+1)→V)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (σ:RawMarkedOutcome V U Γ Color):
    let H₀:=fun (_:V) (_:U)=>True
    let Hₖ:=fun (_:V) (_:U)=>True
    let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ=>
      weight W.1.val/(D*p^m*k*(s W.2.val j)^m);
    (∀ root,|typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) root-
        ∑W,(if root∈typedMarkedOccurrenceResources W then seed W else 0)*
          ∏a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p k q s g j a|<t)→
    (∀x v,q v g≠0→|typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ)
        (rawMarkedPairSpokes π d σ g j) (Sum.inr (true,x,v))-1|<t+τ) ∧
    (∀x v,|typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ)
        (rawMarkedPairSpokes π d σ g j) (Sum.inr (false,x,v))-(m:ℝ)*q v g/s v j|<t+τ*((m:ℝ)*q v g/s v j)) ∧
    (∀x y,¬PermutationClose π (3*d) x y→P.Adj x (π y)→
      |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j)
        (Sum.inl (Sum.inr (x,y)))-1|<t+τ) ∧
    (∀x y,¬PermutationClose π (3*d) x y→P.Adj x y→
      |typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j)
        (Sum.inl (Sum.inl (x,y)))-(m:ℝ)*k/p|<t+τ*((m:ℝ)*k/p)) :=by
  intro H₀ Hₖ seed hconc
  refine ⟨?_,?_,?_,?_⟩
  · exact rawMarked_variable_marked_spoke_concentration_target P π p k hp hk hsum d hd q hq hQ s hs hS
      hnoshort m hm g j D τ A B t hD hspos weight hw σ hconc
  · exact rawMarked_variable_ordinary_spoke_concentration_target P π p k hp hk hsum d hd q hq hQ s hs hS
      hnoshort m hm g j D τ A B t hD hspos weight hw σ hconc
  · exact rawMarked_closing_arc_concentration_target P π p k hp hk hsum d hd q hq hQ s hs hS
      hnoshort m hm g j D τ A B t hD hspos hbalance weight hw σ hconc
  · exact rawMarked_ordinary_arc_concentration_target P π p k hp hk hsum d hd q hq hQ s hs hS
      hnoshort m hm g j D τ A B t hD hspos hbalance weight hw σ hconc
end Oberwolfach
