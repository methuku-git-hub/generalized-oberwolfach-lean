module

public import Oberwolfach.MarkedCapacityCycleWeights

@[expose] public section

/-! Choosing the length threshold before the cycle length. The weight
constants precede the separation parameter, as in the manuscript. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
universe u v w
attribute [local instance] Classical.propDecidable

theorem marked_capacity_cycle_weights_uniform_length (α p₀ : ℝ)
    (hα : 0<α) (hαmax : α≤1) (hp₀ : 0<p₀) (hp₀max : p₀≤1/2) :
    ∃ c₀ : ℕ,∀ k : ℕ,c₀≤k+2 →
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
  let t : ℕ := 1+3*⌈Real.log (10*(100/p₀+1))/(-Real.log (1-α/200))⌉₊
  refine ⟨12*t+4,?_⟩
  intro k hk
  exact marked_capacity_cycle_weights α p₀ hα hαmax hp₀ hp₀max t k le_rfl hk

end Oberwolfach
