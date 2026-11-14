module

public import Oberwolfach.OrdinaryCycleWeightRestriction
public import Oberwolfach.IndexedWheelLoads

@[expose] public section

/-! Restriction of signed weights to their actual cycle family, and the
coefficient bound for an injective lift to wheels at a fixed hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem signed_cycle_test_restrict {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ) (a t : SimpleGraph V → ℝ)
    (hs : ∀ C,a C≠0 → C≤G ∧ IsEmbeddedCycle C r) :
    (∑ C : OrdinaryCycle G r,a C.val.val*t C.val.val)=∑ C : SimpleGraph V,a C*t C := by
  have hzero (C : SimpleGraph V) (hC : ¬(C≤G ∧ IsEmbeddedCycle C r)) : a C=0 := by
    by_contra hn
    exact hC (hs C hn)
  symm
  calc
    _ = ∑ C : EmbeddedCycleFamily V r,a C.val*t C.val := by
      apply finite_sum_restrict_of_zero (fun C => IsEmbeddedCycle C r)
      intro C hC
      rw [hzero C (fun h => hC h.2),zero_mul]
    _ = _ := by
      apply finite_sum_restrict_of_zero (fun C : EmbeddedCycleFamily V r => C.val≤G)
      intro C hC
      rw [hzero C.val (fun h => hC h.1),zero_mul]

theorem indexedWheelWeight_injective_bound {V U I : Type*} [Fintype I]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (W : I → OrdinaryWheel Q F H r) (hW : Function.Injective W) (a : I → ℝ)
    (B : ℝ) (hB : 0≤B) (ha : ∀ i,|a i|≤B) (D : OrdinaryWheel Q F H r) :
    |indexedWheelWeight W a D|≤B := by
  classical
  by_cases hD : D∈Set.range W
  · obtain ⟨i,rfl⟩ := hD
    have he : indexedWheelWeight W a (W i)=a i := by
      unfold indexedWheelWeight
      simp only [hW.eq_iff,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    rw [he]
    exact ha i
  · have hz : indexedWheelWeight W a D=0 := by
      unfold indexedWheelWeight
      apply Finset.sum_eq_zero
      intro i _
      exact if_neg (fun h => hD ⟨i,h⟩)
    rw [hz,abs_zero]
    exact hB

end Oberwolfach
