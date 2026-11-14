module

public import Oberwolfach.MarkedCapacityApproximation
public import Oberwolfach.PositiveMarkedCycleWeights

@[expose] public section

/-! The marked-capacity theorem on canonical typed cycles. All ingredients,
including approximation on every nearby balanced target, are discharged
from the original graph hypotheses. Only the final size threshold depends
on the separation parameter. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
universe u v w
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 2400000 in
theorem marked_capacity_cycle_weights (α p₀ : ℝ) (hα : 0<α) (hαmax : α≤1)
    (hp₀ : 0<p₀) (hp₀max : p₀≤1/2) (t k : ℕ)
    (ht : 1+3*⌈Real.log (10*(100/p₀+1))/(-Real.log (1-α/200))⌉₊≤t)
    (hc : 12*t+4≤k+2) :
    ∃ ε κ a A : ℝ,0<ε ∧ 0<κ ∧ 0<a ∧ 0<A ∧
    ∀ b : ℕ,∃ n₀ : ℕ,
    ∀ (V : Type u) (E : Type v) (K : Type w)
      [Fintype V] [Fintype E] [Fintype K] [DecidableEq V],
    ∀ (tail head : E → V) (ktail khead : K → V),
    Function.Injective (fun e => (tail e,head e)) →
    Function.Injective (fun e => (ktail e,khead e)) →
    ∀ (p D : ℝ),p₀≤p → p≤1/2 → n₀≤Fintype.card V →
    (Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
    (∀ x,|occurrenceDegree tail x-p*D|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree head x-p*D|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree ktail x-p*D/(k+1:ℝ)|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree khead x-p*D/(k+1:ℝ)|≤ε*Fintype.card V) →
    (∀ x y,x≠y → α*p^2*Fintype.card V≤
      ((Finset.univ.filter (fun z => (∃ e,tail e=x ∧ head e=z) ∧ (∃ e,tail e=z ∧ head e=y))).card:ℝ)) →
    (∀ S T : Finset V,(1-2*min (α/16) (p/128))*Fintype.card V<(S.card:ℝ)+T.card →
      (α*p/16)*Fintype.card V*min (S.card:ℝ) T.card≤
      ((Finset.univ.filter (fun e => tail e∈S ∧ head e∈T)).card:ℝ)) →
    ∀ π : Equiv.Perm V,
    (∀ e,¬PermutationClose π b (tail e) (head e)) →
    (∀ e,¬PermutationClose π b (ktail e) (khead e)) →
    ∀ w : E⊕K → ℝ,w∈markedBalanceSubspace tail head ktail khead (k+1) →
    ‖w-(fun _ => (1:ℝ))‖≤κ →
    ∃ q : MarkedCycleTuple tail head ktail khead (k+1) π b → ℝ,
      (∀ C,0<q C ∧ a/(Fintype.card V:ℝ)^k≤q C ∧ q C≤A/(Fintype.card V:ℝ)^k) ∧
      (∑ C,q C • markedCycleIncidence tail head ktail khead (k+1) C.val)=w := by
  obtain ⟨ε,κ,B,hε,hκ,hκsmall,hB,happrox⟩ := marked_capacity_approximation α p₀ hα hαmax hp₀ hp₀max t k ht hc
  let a := κ/(4*(k+1:ℝ))
  have ha : 0<a := by dsimp [a];positivity
  refine ⟨ε,κ/4,a,a+B,hε,by positivity,ha,add_pos ha hB,?_⟩
  intro b
  let C : ℝ := (k+1:ℝ)*((k+2:ℝ)^2*(2*b+1)*B)
  let N : ℕ := ⌈max (10/p₀) (4*C/κ)⌉₊+1
  refine ⟨N,?_⟩
  intro V E K instV instE instK instDec tail head ktail khead hinj hkinj p D hp hpmax hN hDlo hDhi hdt hdh hdkt hdkh hcommon hcut π hsep hksep w hw hwclose
  have hn : 0<Fintype.card V := by dsimp only [N] at hN;omega
  have hnr : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have hNreal : (⌈max (10/p₀) (4*C/κ)⌉₊:ℝ)+1≤Fintype.card V := by
    exact_mod_cast hN
  have hceil := Nat.le_ceil (max (10/p₀) (4*C/κ))
  have hsize : 10/p₀≤(Fintype.card V:ℝ) := by
    have hh := (le_max_left (10/p₀) (4*C/κ)).trans hceil
    linarith
  have herr : C/(Fintype.card V:ℝ)<κ/4 := by
    have hh := (le_max_right (10/p₀) (4*C/κ)).trans hceil
    have hlt : 4*C/κ<(Fintype.card V:ℝ) := by linarith
    have hm := (div_lt_iff₀ hκ).mp hlt
    apply (div_lt_iff₀ hnr).mpr
    nlinarith
  obtain ⟨q,hq,he⟩ := exact_positive_marked_cycle_weights tail head ktail khead hinj hkinj
    (k+1) (by omega) π b hn w κ (C/(Fintype.card V:ℝ)) B hκ herr hw hwclose
    (by
      intro w' hw' hw'close
      obtain ⟨q,hq,he⟩ := happrox V E K tail head ktail khead hinj hkinj p D hp hpmax hn hsize hDlo hDhi
        hdt hdh hdkt hdkh hcommon hcut π b hsep hksep w' hw' hw'close
      refine ⟨q,?_,he⟩
      simpa only [Nat.add_sub_cancel] using hq)
  refine ⟨q,?_,he⟩
  simpa only [a,Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel] using hq

end Oberwolfach
