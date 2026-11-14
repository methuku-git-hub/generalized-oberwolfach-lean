module

public import Mathlib.Tactic

@[expose] public section

/-! Physical incidence bounds in an arbitrary ambient vertex set. The
permutation need not preserve the original rim vertex subset. Both
incidences of a loop are counted. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem injective_fiber_sum_le {X Z : Type*} [Fintype X]
    (f : X → Z) (hf : Function.Injective f) (g : X → ℝ) {B : ℝ}
    (hB : 0≤B) (hg : ∀ x,g x≤B) (z : Z) :
    (∑ x,if f x=z then g x else 0)≤B := by
  classical
  by_cases hz : ∃ x,f x=z
  · obtain ⟨x,hx⟩ := hz
    calc
      _ = g x := by
        rw [Finset.sum_eq_single x]
        · simp only [hx,ite_true]
        · intro y _ hy
          have hh : f y≠z := fun he=>hy (hf (he.trans hx.symm))
          simp only [hh,ite_false]
        · simp
      _ ≤ B := hg x
  · have hz' : ∀ x,f x≠z := by simpa only [not_exists] using hz
    simpa only [hz',ite_false,Finset.sum_const_zero] using hB

theorem typed_physical_incidence_bound {X Y Z : Type*} [Fintype X] [Fintype Y]
    (J : X → Y → ℕ) (f : X → Z) (g : Y → Z)
    (hf : Function.Injective f) (hg : Function.Injective g) {B : ℝ}
    (hB : 0≤B) (hrow : ∀ x,(∑ y,(J x y : ℝ))≤B)
    (hcol : ∀ y,(∑ x,(J x y : ℝ))≤B) (z : Z) :
    (∑ x,∑ y,(J x y : ℝ)*((if f x=z then 1 else 0)+(if g y=z then 1 else 0)))≤2*B := by
  have h1 := injective_fiber_sum_le f hf (fun x=>∑ y,(J x y : ℝ)) hB hrow z
  have h2 := injective_fiber_sum_le g hg (fun y=>∑ x,(J x y : ℝ)) hB hcol z
  have he : (∑ x,∑ y,(J x y : ℝ)*((if f x=z then 1 else 0)+(if g y=z then 1 else 0)))=
      (∑ x,if f x=z then (∑ y,(J x y : ℝ)) else 0)+
      (∑ y,if g y=z then (∑ x,(J x y : ℝ)) else 0) := by
    simp only [mul_add,Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro x _
      by_cases hx : f x=z <;> simp only [hx,ite_true,ite_false,mul_one,mul_zero,Finset.sum_const_zero]
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : g y=z <;> simp only [hy,ite_true,ite_false,mul_one,mul_zero,Finset.sum_const_zero]
  rw [he]
  linarith only [h1,h2]

theorem marked_permuted_incidence_bound {V Z : Type*} [Fintype V]
    (J : V → V → ℕ) (ι : V → Z) (hι : Function.Injective ι) (π : Equiv.Perm Z)
    {B : ℝ} (hB : 0≤B) (hrow : ∀ v,(∑ w,(J v w : ℝ))≤B)
    (hcol : ∀ v,(∑ w,(J w v : ℝ))≤B) (z : Z) :
    (∑ x,∑ y,(J x y : ℝ)*((if ι x=z then 1 else 0)+(if π (ι y)=z then 1 else 0)))≤2*B :=
  typed_physical_incidence_bound J ι (π ∘ ι) hι (π.injective.comp hι) hB hrow hcol z

end Oberwolfach
