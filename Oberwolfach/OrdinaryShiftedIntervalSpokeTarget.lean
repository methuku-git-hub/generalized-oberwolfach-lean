module

public import Oberwolfach.OrdinaryShiftedIntervalSpokeExpectation
public import Oberwolfach.MarkedFullSpokeWeightedSum
public import Oberwolfach.MarkedSuccessorPositionalSum
public import Oberwolfach.SuccessorSequencePositionBounds

@[expose] public section
/-! At a positive marked-spoke root, the variable-hub seed expectation
has the target value up to the original positional error. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_shifted_interval_spoke_target
    (P:SimpleGraph V) (π:Equiv.Perm V)
    (p k:ℝ) (hp:0<p) (hk:0≤k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (m:ℕ) (hm:2≤m) (g:Γ) (j:Color) (D τ A B:ℝ) (hD:0<D)
    (hspos:∀ u,0<s u j)
    (weight:(Fin (m+1)→V)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (x:V) (u:U) (hqu:q u g≠0):
    let H₀:=fun (_:V) (_:U)=>True
    let Hₖ:=fun (_:V) (_:U)=>True
    let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ=>
      weight W.1.val/(D*p^(m+1)*(s W.2.val j)^m)
    let mean:=(FiniteLaw.pi (rawMarkedWheelLaw p k hp.le hk hsum d hd q hq hQ s hs hS)).expectation
      (fun σ=>typedMarkedPotentialLoad seed (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) (Sum.inr (true,x,u)));
    1-τ≤mean ∧ mean≤1 :=by
  intro H₀ Hₖ seed mean
  have hsupport:∀ W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ,
      weight W.1.val≠0→(∀ i:Fin m,P.Adj (W.1.val i.castSucc) (W.1.val i.succ)) ∧
        P.Adj (W.1.val (Fin.last m)) (π (W.1.val 0)):=by
    intro W hW
    exact successor_weight_parent_edges hw W.1.val hW
  have hmean:=ordinary_shifted_interval_spoke_expectation P π p k hp hk hsum d hd q hq hQ s hs hS
    hnoshort m hm H₀ Hₖ g j D hD hspos (fun W=>weight W.1.val) hsupport x u hqu
  have hsum:
      (∑ W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ,
        if Sum.inr (true,x,u)∈typedMarkedOccurrenceResources W then weight W.1.val/D else 0)=
      (∑ C:MarkedCycleTuple (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d),
        if C.val 0=x then weight C.val else 0)/D :=by
    have hmatch:=marked_full_spoke_weighted_sum (fun C:MarkedCycleTuple (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)=>weight C.val) x u
    calc
      _ = (∑ W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ,
        if Sum.inr (true,x,u)∈typedMarkedOccurrenceResources W then weight W.1.val else 0)/D := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro W _
          split_ifs <;> simp
      _ = _ := by
        apply congrArg (fun z:ℝ=>z/D)
        convert hmatch using 1
        apply Finset.sum_congr rfl
        intro W _
        split_ifs <;> rfl
  have hpos:=successor_weight_marked_cycle_position P π m (3*d) D τ A B weight hw x
  have heq:mean=(∑ C:MarkedCycleTuple (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d),
        if C.val 0=x then weight C.val else 0)/D:=by
    rw [←hsum]
    exact hmean
  rw [heq]
  constructor
  · exact (le_div_iff₀ hD).2 (by linarith [hpos.1])
  · exact (div_le_iff₀ hD).2 (by linarith [hpos.2])
end Oberwolfach
