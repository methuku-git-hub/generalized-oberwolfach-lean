module

public import Oberwolfach.OrdinaryShiftedSeedExpectation
public import Oberwolfach.MarkedFullRimWeightedSum
public import Oberwolfach.MarkedClosingArcIndicator
public import Oberwolfach.MarkedSuccessorAnyArcSum
public import Oberwolfach.SuccessorSequencePositionBounds

@[expose] public section
/-! The closing marked physical arc has auxiliary head z and physical head π z. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_shifted_closing_arc_target
    (P:SimpleGraph V) (π:Equiv.Perm V)
    (p k:ℝ) (hp:0<p) (hk:0≤k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (m:ℕ) (hm:2≤m) (g:Γ) (j:Color) (D τ A B:ℝ) (hD:0<D)
    (hspos:∀ u,0<s u j) (t:ℝ) (ht:0≤t) (hbalance:∑ u,q u g=D*t)
    (weight:(Fin (m+1)→V)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (x z:V) (hclose:¬PermutationClose π (3*d) x z) (hP:P.Adj x (π z)):
    let H₀:=fun (_:V) (_:U)=>True
    let Hₖ:=fun (_:V) (_:U)=>True
    let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ=>
      weight W.1.val/(D*p^(m+1)*(s W.2.val j)^m)
    let mean:=(FiniteLaw.pi (rawMarkedWheelLaw p k hp.le hk hsum d hd q hq hQ s hs hS)).expectation
      (fun σ=>typedMarkedPotentialLoad seed (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) (Sum.inl (Sum.inr (x,z))));
    (1-τ)*t/p≤mean ∧ mean≤t/p :=by
  intro H₀ Hₖ seed mean
  let root:((V×V)⊕(V×V))⊕(Bool×V×U):=Sum.inl (Sum.inr (x,z))
  have hroot:rawMarkedWheelMarginal P π d p p q s g j root≠0 :=by
    simp [root,rawMarkedWheelMarginal,hclose,hP,hp.ne']
  have hsupport:∀ W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ,
      weight W.1.val≠0→(∀ i:Fin m,P.Adj (W.1.val i.castSucc) (W.1.val i.succ)) ∧
        P.Adj (W.1.val (Fin.last m)) (π (W.1.val 0)):=by
    intro W hW
    exact successor_weight_parent_edges hw W.1.val hW
  have hmean:=ordinary_shifted_seed_expectation P π p k hp hk hsum d hd q hq hQ s hs hS
    hnoshort m hm H₀ Hₖ g j D hD hspos (fun W=>weight W.1.val) hsupport root hroot
  change mean = _ at hmean
  have hrootval:rawMarkedWheelMarginal P π d p p q s g j root=p:=by
    simp [root,rawMarkedWheelMarginal,hclose,hP]
  rw [hrootval] at hmean
  have hsum:=marked_full_rim_weighted_sum
    (fun C:MarkedCycleTuple (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)=>weight C.val)
    (fun u=>q u g) (Sum.inr (x,z))
  have hmean' : mean = (∑ C:MarkedCycleTuple (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d),
        if C.val (Fin.last m)=x ∧ C.val 0=z then weight C.val else 0)*(t/p) :=by
    rw [hmean]
    calc
      _ = (∑ W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ,
          if root∈typedMarkedOccurrenceResources W then weight W.1.val*q W.2.val g else 0)/(D*p) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro W _
        split_ifs <;> simp
      _ = (∑ C:MarkedCycleTuple (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d),
          if CanonicalMarkedArcMem C (Sum.inr (x,z)) then weight C.val else 0)*(∑ u,q u g)/(D*p) :=by
        congr 1
        convert hsum using 1
        apply Finset.sum_congr rfl
        intro W _
        split_ifs <;> rfl
      _ = _ :=by
        rw [hbalance]
        have heq:(∑ C:MarkedCycleTuple (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d),
            if CanonicalMarkedArcMem C (Sum.inr (x,z)) then weight C.val else 0)=
          ∑ C:MarkedCycleTuple (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d),
            if C.val (Fin.last m)=x ∧ C.val 0=z then weight C.val else 0 :=by
          apply Finset.sum_congr rfl
          intro C _
          have hh:=marked_closing_arc_iff C x z
          split_ifs <;> simp_all
        rw [heq]
        field_simp
        <;> ring

  have hh:=successor_weight_marked_cycle_any_arc P π m (3*d) D τ A B weight hw (Fin.last m) x z hclose (by simpa using hP)
  simp only [cycleNext_last] at hh
  have hfac:0≤t/p:=div_nonneg ht hp.le
  have hlo:=mul_le_mul_of_nonneg_right hh.1 hfac
  have hhi:=mul_le_mul_of_nonneg_right hh.2 hfac
  rw [hmean']
  constructor
  · simpa only [mul_div_assoc] using hlo
  · simpa only [one_mul] using hhi
end Oberwolfach
