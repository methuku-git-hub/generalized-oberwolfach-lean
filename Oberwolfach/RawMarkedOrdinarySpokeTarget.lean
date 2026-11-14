module

public import Oberwolfach.RawMarkedVariableOrdinarySpokeExpectation
public import Oberwolfach.MarkedFullOrdinarySpokeSum
public import Oberwolfach.MarkedSuccessorAnyPositionalSum
public import Oberwolfach.SuccessorSequencePositionBounds

@[expose] public section
/-! The marked cycles give one explicitly quantified part of the load
at an ordinary spoke.  The remaining part comes from ordinary cycles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem rawMarked_variable_ordinary_spoke_target
    (P:SimpleGraph V) (π:Equiv.Perm V)
    (p k:ℝ) (hp:0<p) (hk:0<k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (m:ℕ) (hm:2≤m) (g:Γ) (j:Color) (D τ A B:ℝ) (hD:0<D)
    (hspos:∀ u,0<s u j)
    (weight:(Fin (m+1)→V)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (x:V) (u:U):
    let H₀:=fun (_:V) (_:U)=>True
    let Hₖ:=fun (_:V) (_:U)=>True
    let seed:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ=>
      weight W.1.val/(D*p^m*k*(s W.2.val j)^m)
    let mean:=(FiniteLaw.pi (rawMarkedWheelLaw p k hp.le hk.le hsum d hd q hq hQ s hs hS)).expectation
      (fun σ=>typedMarkedPotentialLoad seed (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) (Sum.inr (false,x,u)));
    (1-τ)*(m:ℝ)*q u g/s u j≤mean ∧ mean≤(m:ℝ)*q u g/s u j :=by
  intro H₀ Hₖ seed mean
  have hsupport:∀ W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ,
      weight W.1.val≠0→(∀ i:Fin m,P.Adj (W.1.val i.castSucc) (W.1.val i.succ)) ∧
        P.Adj (W.1.val (Fin.last m)) (π (W.1.val 0)):=by
    intro W hW
    exact successor_weight_parent_edges hw W.1.val hW
  have hmean:=rawMarkedSeed_variable_ordinary_spoke_expectation P π p k hp hk hsum d hd q hq hQ s hs hS
    hnoshort m hm H₀ Hₖ g j D hD hspos (fun W=>weight W.1.val) hsupport x u
  change mean = _ at hmean
  let S:ℝ:=∑ i:Fin m,∑ C:MarkedCycleTuple (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d),
    if C.val i.succ=x then weight C.val else 0
  have hsumlo:(m:ℝ)*((1-τ)*D)≤S:=by
    have hh:∑ _i:Fin m,((1-τ)*D)≤S:=by
      apply Finset.sum_le_sum
      intro i _
      exact (successor_weight_marked_cycle_any_position P π m (3*d) D τ A B weight hw i.succ x).1
    simpa [S] using hh
  have hsumhi:S≤(m:ℝ)*D:=by
    have hh:S≤∑ _i:Fin m,D:=by
      apply Finset.sum_le_sum
      intro i _
      exact (successor_weight_marked_cycle_any_position P π m (3*d) D τ A B weight hw i.succ x).2
    simpa [S] using hh
  have hmean':mean=S*(q u g/(D*s u j)):=by
    rw [hmean]
    have hsumeq:=marked_full_ordinary_spoke_weighted_sum
      (fun C:MarkedCycleTuple (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)=>weight C.val) x u
    calc
      _ = (∑ W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ,
        if Sum.inr (false,x,u)∈typedMarkedOccurrenceResources W then weight W.1.val else 0)*(q u g/(D*s u j)):=by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro W _
          split_ifs <;> simp only [mul_div_assoc,zero_mul]
      _ = _ := by
        have he : (∑ W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ,
            if Sum.inr (false,x,u)∈typedMarkedOccurrenceResources W then weight W.1.val else 0)=S := by
          dsimp [S]
          convert hsumeq using 1
          apply Finset.sum_congr rfl
          intro W _
          split_ifs <;> rfl
        rw [he]
  have hfac:0≤q u g/(D*s u j):=div_nonneg (hq u g) (mul_nonneg hD.le (hspos u).le)
  have hlo:=mul_le_mul_of_nonneg_right hsumlo hfac
  have hhi:=mul_le_mul_of_nonneg_right hsumhi hfac
  have helo:((m:ℝ)*((1-τ)*D))*(q u g/(D*s u j))=(1-τ)*(m:ℝ)*q u g/s u j:=by
    field_simp
    <;> ring
  have hehi:((m:ℝ)*D)*(q u g/(D*s u j))=(m:ℝ)*q u g/s u j:=by
    field_simp
    <;> ring
  rw [←helo,←hehi,hmean']
  exact ⟨hlo,hhi⟩
end Oberwolfach
