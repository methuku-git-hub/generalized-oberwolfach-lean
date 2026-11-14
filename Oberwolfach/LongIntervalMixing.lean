module

public import Oberwolfach.TransitionMixingScale
public import Oberwolfach.ExceptionalInterfaceIntervals

@[expose] public section

/-! A single exceptional interface may occur before or after a mixing block.
The interval product still has the same relative estimate at its own endpoint. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem transitionWalk_mixing_from_subinterval {X : Type*} [Fintype X]
    (R : ℕ → X → X → ℝ) (π : ℕ → X → ℝ)
    (hR : ∀ i, IsTransition (R i))
    (hπ : ∀ i, transitionApply (π i) (R i) = π (i+1))
    (a L s t : ℕ) (has : a ≤ s) (hst : s+t ≤ a+L) (ε : ℝ)
    (hblock : ∀ x, RelativeError (transitionWalk R s t x) (π (s+t)) ε) :
    ∀ x, RelativeError (transitionWalk R a L x) (π (a+L)) ε := by
  have ha : a+(s-a)=s := Nat.add_sub_of_le has
  have hfirst : transitionCompose (transitionWalk R a (s-a)) (transitionWalk R s t) =
      transitionWalk R a ((s-a)+t) := by
    simpa only [ha] using (transitionWalk_add R a (s-a) t).symm
  have hstart : a+((s-a)+t)=s+t := by omega
  have hfull : transitionCompose
      (transitionCompose (transitionWalk R a (s-a)) (transitionWalk R s t))
      (transitionWalk R (s+t) (a+L-(s+t))) = transitionWalk R a L := by
    rw [hfirst]
    have hh := (transitionWalk_add R a ((s-a)+t) (a+L-(s+t))).symm
    rw [hstart] at hh
    convert hh using 1 <;> congr 1 <;> omega
  intro x
  have hh := mixed_block_with_prefix_suffix (transitionWalk R a (s-a)) (transitionWalk R s t)
    (transitionWalk R (s+t) (a+L-(s+t))) (π (s+t)) ε
    (transitionWalk_isTransition R hR _ _) (transitionWalk_isTransition R hR _ _).1 hblock x
  have hstat := transitionWalk_stationary R π hπ (s+t) (a+L-(s+t))
  have hend : s+t+(a+L-(s+t))=a+L := Nat.add_sub_of_le hst
  rw [hend] at hstat
  rw [hfull,hstat] at hh
  exact hh

theorem clean_block_mixing {X : Type*} [Fintype X]
    (R : ℕ → X → X → ℝ) (π : ℕ → X → ℝ)
    (hR : ∀ i, IsTransition (R i)) (hπ0 : ∀ i x, 0 ≤ π i x)
    (hπsum : ∀ i, ∑ x, π i x = 1)
    (hπ : ∀ i, transitionApply (π i) (R i) = π (i+1))
    (J : Finset ℕ) (κ B : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) (hB : 1 ≤ B)
    (a t : ℕ)
    (hupper : ∀ i, a ≤ i → i < a+t → i ∉ J → ∀ x y, R i x y ≤ B*π (i+1) y)
    (hminor : ∀ i, a ≤ i → i+3 ≤ a+t → i ∉ J → i+1 ∉ J → i+2 ∉ J →
      ∀ x y, κ*π (i+3) y ≤ transitionWalk R i 3 x y)
    (ht : 1+3*⌈Real.log (10*(B+1)) / (-Real.log (1-κ))⌉₊ ≤ t)
    (hclean : ∀ j, a ≤ j → j < a+t → j ∉ J) :
    ∀ x, RelativeError (transitionWalk R a t x) (π (a+t)) (1/10) := by
  let q := ⌈Real.log (10*(B+1)) / (-Real.log (1-κ))⌉₊
  apply transition_segment_mixing R π hR hπ0 hπsum hπ a t q κ B (1/10) (by linarith)
    (by dsimp [q]; omega) (hupper a le_rfl (by omega) (hclean a le_rfl (by omega)))
  · intro j hj x y
    have hq : 1+3*q ≤ t := ht
    have h0 := hclean (a+1+j*3) (by omega) (by omega)
    have h1 := hclean (a+1+j*3+1) (by omega) (by omega)
    have h2 := hclean (a+1+j*3+2) (by omega) (by omega)
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using
      hminor (a+1+j*3) (by omega) (by omega) h0 h1 h2 x y
  · exact long_capacity_mixing_steps κ B hκ hκ1 hB

theorem long_interval_mixing {X : Type*} [Fintype X]
    (R : ℕ → X → X → ℝ) (π : ℕ → X → ℝ)
    (hR : ∀ i, IsTransition (R i)) (hπ0 : ∀ i x, 0 ≤ π i x)
    (hπsum : ∀ i, ∑ x, π i x = 1)
    (hπ : ∀ i, transitionApply (π i) (R i) = π (i+1))
    (J : Finset ℕ) (hJ : J.card ≤ 1) (κ B : ℝ)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hB : 1 ≤ B)
    (a L t : ℕ)
    (hupper : ∀ i, a ≤ i → i < a+L → i ∉ J → ∀ x y, R i x y ≤ B*π (i+1) y)
    (hminor : ∀ i, a ≤ i → i+3 ≤ a+L → i ∉ J → i+1 ∉ J → i+2 ∉ J →
      ∀ x y, κ*π (i+3) y ≤ transitionWalk R i 3 x y)
    (ht : 1+3*⌈Real.log (10*(B+1)) / (-Real.log (1-κ))⌉₊ ≤ t)
    (hL : 2*t ≤ L) :
    ∀ x, RelativeError (transitionWalk R a L x) (π (a+L)) (1/10) := by
  obtain ⟨s,has,hst,hclean⟩ := two_blocks_one_exception J hJ a L t hL
  exact transitionWalk_mixing_from_subinterval R π hR hπ a L s t has hst (1/10)
    (clean_block_mixing R π hR hπ0 hπsum hπ J κ B hκ hκ1 hB s t
      (fun i hi hiend => hupper i (by omega) (by omega))
      (fun i hi hiend => hminor i (by omega) (by omega)) ht hclean)

end Oberwolfach
