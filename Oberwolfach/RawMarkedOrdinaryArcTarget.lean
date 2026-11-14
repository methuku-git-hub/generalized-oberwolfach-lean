module

public import Oberwolfach.RawMarkedSeedVariableExpectation
public import Oberwolfach.MarkedFullRimWeightedSum
public import Oberwolfach.MarkedOrdinaryArcWeightedSum
public import Oberwolfach.MarkedSuccessorAnyArcSum
public import Oberwolfach.SuccessorSequencePositionBounds

@[expose] public section
/-! The marked-cycle contribution at an ordinary physical arc. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem rawMarked_ordinary_arc_target
    (P:SimpleGraph V) (π:Equiv.Perm V)
    (p k:ℝ) (hp:0<p) (hk:0<k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (m:ℕ) (hm:2≤m) (g:Γ) (j:Color) (D τ A B:ℝ) (hD:0<D)
    (hspos:∀ u,0<s u j) (hbalance:∑ u,q u g=D*k)
    (weight:(Fin (m+1)→V)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (x z:V) (hclose:¬PermutationClose π (3*d) x z) (hP:P.Adj x z):
    let H₀:=fun (_:V) (_:U)=>True
    let Hₖ:=fun (_:V) (_:U)=>True
    let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ=>
      weight W.1.val/(D*p^m*k*(s W.2.val j)^m)
    let mean:=(FiniteLaw.pi (rawMarkedWheelLaw p k hp.le hk.le hsum d hd q hq hQ s hs hS)).expectation
      (fun σ=>typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) (Sum.inl (Sum.inl (x,z))));
    (1-τ)*(m:ℝ)*k/p≤mean ∧ mean≤(m:ℝ)*k/p :=by
  intro H₀ Hₖ seed mean
  let root:((V×V)⊕(V×V))⊕(Bool×V×U):=Sum.inl (Sum.inl (x,z))
  have hroot:rawMarkedWheelMarginal P π d p k q s g j root≠0 :=by
    simp [root,rawMarkedWheelMarginal,hclose,hP,hp.ne']
  have hsupport:∀ W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ,
      weight W.1.val≠0→(∀ i:Fin m,P.Adj (W.1.val i.castSucc) (W.1.val i.succ)) ∧
        P.Adj (W.1.val (Fin.last m)) (π (W.1.val 0)):=by
    intro W hW
    exact successor_weight_parent_edges hw W.1.val hW
  have hmean:=rawMarkedSeed_variable_hub_expectation P π p k hp hk hsum d hd q hq hQ s hs hS
    hnoshort m hm H₀ Hₖ g j D hD hspos (fun W=>weight W.1.val) hsupport root hroot
  change mean = _ at hmean
  have hrootval:rawMarkedWheelMarginal P π d p k q s g j root=p:=by
    simp [root,rawMarkedWheelMarginal,hclose,hP]
  rw [hrootval] at hmean
  have hsum:=marked_full_rim_weighted_sum
    (fun C:MarkedCycleTuple (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)=>weight C.val)
    (fun u=>q u g) (Sum.inl (x,z))
  let S:ℝ:=∑ i:Fin m,∑ C:MarkedCycleTuple (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d),
    if C.val i.castSucc=x ∧ C.val i.succ=z then weight C.val else 0
  have hpos (i:Fin m):1-τ≤(∑ C:MarkedCycleTuple (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d),
      if C.val i.castSucc=x ∧ C.val i.succ=z then weight C.val else 0) ∧
      (∑ C:MarkedCycleTuple (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d),
      if C.val i.castSucc=x ∧ C.val i.succ=z then weight C.val else 0)≤1:=by
    have hh:=successor_weight_marked_cycle_any_arc P π m (3*d) D τ A B weight hw i.castSucc x z hclose (by
      simpa only [Fin.val_castSucc,show i.val+1≠m+1 by omega,ite_false] using hP)
    simpa only [cycleNext_castSucc] using hh
  have hsumlo:(m:ℝ)*(1-τ)≤S:=by
    have hh:∑ _i:Fin m,(1-τ)≤S:=by
      apply Finset.sum_le_sum
      intro i _
      exact (hpos i).1
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    exact hh
  have hsumhi:S≤(m:ℝ):=by
    have hh:S≤∑ _i:Fin m,(1:ℝ):=by
      apply Finset.sum_le_sum
      intro i _
      exact (hpos i).2
    simpa [S] using hh
  have hmean':mean=S*(k/p):=by
    rw [hmean]
    calc
      _ = (∑ W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ,
          if root∈typedMarkedOccurrenceResources W then weight W.1.val*q W.2.val g else 0)/(D*p) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro W _
        split_ifs <;> simp
      _ = (∑ C:MarkedCycleTuple (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d),
          if CanonicalMarkedArcMem C (Sum.inl (x,z)) then weight C.val else 0)*(∑ u,q u g)/(D*p) :=by
        congr 1
        convert hsum using 1
        apply Finset.sum_congr rfl
        intro W _
        split_ifs <;> rfl
      _ = S*(k/p) :=by
        rw [hbalance,marked_ordinary_arc_weighted_sum]
        dsimp [S]
        field_simp
        <;> ring
  have hfac:0≤k/p:=div_nonneg hk.le hp.le
  have hlo:=mul_le_mul_of_nonneg_right hsumlo hfac
  have hhi:=mul_le_mul_of_nonneg_right hsumhi hfac
  have helo:((m:ℝ)*(1-τ))*(k/p)=(1-τ)*(m:ℝ)*k/p:=by ring
  have hehi:(m:ℝ)*(k/p)=(m:ℝ)*k/p:=by ring
  rw [←helo,←hehi,hmean']
  exact ⟨hlo,hhi⟩
end Oberwolfach
