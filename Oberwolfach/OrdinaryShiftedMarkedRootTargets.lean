module

public import Oberwolfach.OrdinaryShiftedIntervalSpokeConcentration
public import Oberwolfach.OrdinaryShiftedOrdinarySpokeConcentration
public import Oberwolfach.OrdinaryShiftedOrdinaryArcConcentration
public import Oberwolfach.OrdinaryShiftedClosingArcConcentration
public import Oberwolfach.OrdinaryMixedIdealTarget

@[expose] public section
/-! Convert the all-root marked concentration event to the four ideal
load estimates on the same active typed resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [Fintype I]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_shifted_marked_root_targets
    (P:SimpleGraph V) (π:Equiv.Perm V)
    (p k:ℝ) (hp:0<p) (hk:0≤k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d)
    (q:U→Bool→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (m:ℕ) (hm:2≤m) (D τ A B t:ℝ) (hD:0<D)
    (hspos:∀ u,0<s u true)
    (weight:(Fin (m+1)→V)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (η:I→U→ℝ) (σ:RawMarkedOutcome V U Bool Bool):
    let H₀:=fun (_:V) (_:U)=>True
    let Hₖ:=fun (_:V) (_:U)=>True
    let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ=>
      weight W.1.val/(D*p^(m+1)*(s W.2.val true)^m);
    (∀ root,|typedMarkedPotentialLoad seed (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ true true) root-
        ∑ W,(if root∈typedMarkedOccurrenceResources W then seed W else 0)*
          ∏ a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p p q s true true a|<t)→
    (∀x u,rawMarkedPairSpokes π d σ true true true x u→q u true≠0)→
    ∀ root,Sum.elim (ordinaryShiftedPairRims P π d σ)
      (fun z=>rawMarkedPairSpokes π d σ true true z.1 z.2.1 z.2.2) root→
    |typedMarkedPotentialLoad seed (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ true true) root-
      ordinaryMixedIdealTarget (m:ℝ) D p (fun u=>q u true) (fun u=>s u true) η none root|≤
      t+τ*ordinaryMixedIdealTarget (m:ℝ) D p (fun u=>q u true) (fun u=>s u true) η none root :=by
  intro H₀ Hₖ seed hconc hpositive root hactive
  let κ:ℝ:=(∑u,q u true)/D
  have hκ:0≤κ:=div_nonneg (Finset.sum_nonneg (fun u _=>hq u true)) hD.le
  have hbalance:(∑u,q u true)=D*κ:=by dsimp [κ];field_simp
  cases root with
  | inl a=>
    cases a with
    | inl xy=>
      obtain ⟨x,z⟩:=xy
      have ha : ¬PermutationClose π (3*d) x z ∧ P.Adj x z := by
        simpa only [Sum.elim_inl,ordinaryShiftedPairRims] using And.intro hactive.1 hactive.2.1
      have hh:=ordinary_shifted_ordinary_arc_concentration_target P π p k hp hk hsum d hd q hq hQ s hs hS
        hnoshort m hm true true D τ A B t hD hspos κ hκ hbalance weight hw σ hconc x z ha.1 ha.2
      have heq:(m:ℝ)*κ/p=(m:ℝ)*(∑u,q u true)/(D*p):=by dsimp [κ];ring
      rw [heq] at hh
      simpa only [ordinaryMixedIdealTarget] using hh.le
    | inr xy=>
      obtain ⟨x,z⟩:=xy
      have ha : ¬PermutationClose π (3*d) x z ∧ P.Adj x (π z) := by
        simpa only [Sum.elim_inl,ordinaryShiftedPairRims,Sum.elim_inr] using And.intro hactive.1 hactive.2.1
      have hh:=ordinary_shifted_closing_arc_concentration_target P π p k hp hk hsum d hd q hq hQ s hs hS
        hnoshort m hm true true D τ A B t hD hspos κ hκ hbalance weight hw σ hconc x z ha.1 ha.2
      have heq:κ/p=(∑u,q u true)/(D*p):=by dsimp [κ];ring
      rw [heq] at hh
      simpa only [ordinaryMixedIdealTarget] using hh.le
  | inr z=>
    obtain ⟨b,x,u⟩:=z
    cases b with
    | false=>
      have hh:=ordinary_shifted_ordinary_spoke_concentration_target P π p k hp hk hsum d hd q hq hQ s hs hS
        hnoshort m hm true true D τ A B t hD hspos weight hw σ hconc x u
      simpa only [ordinaryMixedIdealTarget] using hh.le
    | true=>
      have hpq:=hpositive x u hactive
      have hh:=ordinary_shifted_interval_spoke_concentration_target P π p k hp hk hsum d hd q hq hQ s hs hS
        hnoshort m hm true true D τ A B t hD hspos weight hw σ hconc x u hpq
      simpa only [ordinaryMixedIdealTarget,mul_one] using hh.le
end Oberwolfach
