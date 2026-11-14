module

public import Oberwolfach.CyclicCapacityWeights
public import Oberwolfach.DirectedTransversalCycleWeights

@[expose] public section

/-! The complete long-capacity theorem for labelled classes of equal finite
size. Uniform weight coefficients are chosen before n and before the capacities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
universe u
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 1200000 in
theorem long_cyclic_capacity_theorem
    (κ B a₀ a₁ d₀ d₁ : ℝ) (hκ : 0<κ) (hκ1 : κ<1) (hB : 1≤B)
    (ha₀ : 0<a₀) (ha₁ : 0<a₁) (hd₀ : 0<d₀) (hd₁ : 0<d₁)
    (t : ℕ) (ht : 1+3*⌈Real.log (10*(B+1))/(-Real.log (1-κ))⌉₊ ≤ t)
    (c : ℕ) (hc : 12*t+4≤c) :
    ∃ b₀ b₁ : ℝ,0<b₀ ∧ 0<b₁ ∧
    ∀ n : ℕ,1≤n →
    ∀ (X : Type u) [Fintype X],Fintype.card X=n →
    ∀ (a : Fin c → X → X → ℝ) (d : Fin c → X → ℝ),
    (∀ i x y,0≤a i x y) →
    (∀ i x,∑ y,a i x y=d i x) →
    (∀ i y,∑ x,a i x y=d (finRotate c i) y) →
    (∀ i x y,0<a i x y → a₀ ≤ a i x y ∧ a i x y ≤ a₁) →
    (∀ i x,d₀*n ≤ d i x ∧ d i x ≤ d₁*n) →
    ∀ J : Finset (Fin c),J.card≤1 →
    (∀ i,i∉J → ∀ x y,cyclicCapacityTransition a d i x y ≤
      B*(d (finRotate c i) y/(∑ z,d ⟨0,by omega⟩ z))) →
    (∀ i,i∉J → finRotate c i∉J → finRotate c (finRotate c i)∉J →
      ∀ x z,κ*(d (finRotate c (finRotate c (finRotate c i))) z/(∑ z,d ⟨0,by omega⟩ z)) ≤
        ∑ y,∑ w,cyclicCapacityTransition a d i x y*cyclicCapacityTransition a d (finRotate c i) y w*
          cyclicCapacityTransition a d (finRotate c (finRotate c i)) w z) →
    ∃ wC : DirectedTransversalCycle a → ℝ,
      (∀ C,0<wC C) ∧
      (∀ i x y,(∑ C,if C.val i=x ∧ C.val (finRotate c i)=y then wC C else 0)=a i x y) ∧
      (∀ C,b₀/(n:ℝ)^(c-2) ≤ wC C ∧ wC C ≤ b₁/(n:ℝ)^(c-2)) := by
  obtain ⟨L,hL,hsum⟩ := three_long_intervals c t hc
  subst c
  letI : NeZero (∑ i,L i) := ⟨by omega⟩
  refine ⟨longCycleLower L a₀ d₀ d₁,longCycleUpper L a₁ d₀ d₁,
    longCycleLower_pos L a₀ d₀ d₁ ha₀ hd₀ hd₁,longCycleUpper_pos L a₁ d₀ d₁ ha₁ hd₀ hd₁,?_⟩
  intro n hn X inst hcard a d ha hrow hcol hapos hdscale J hJ hupper hminor
  letI : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hnr : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  obtain ⟨w,hw,he,hz,hbounds⟩ := cyclic_capacity_three_interval_weights L t hL a d ha hrow hcol
    n a₀ a₁ d₀ d₁ (by exact_mod_cast hcard) hnr ha₀ ha₁ hd₀ hd₁ hapos hdscale J hJ κ B hκ hκ1 hB ht hupper hminor
  refine ⟨fun C => w C.val,?_,?_,?_⟩
  · intro C
    exact (div_pos (longCycleLower_pos L a₀ d₀ d₁ ha₀ hd₀ hd₁) (pow_pos hnr _)).trans_le
      (hbounds C.val C.property).1
  · exact directed_transversal_weight_restriction a ha w hz he
  · intro C
    exact hbounds C.val C.property

end Oberwolfach
