module

public import Oberwolfach.SeparatedWeightRestriction
public import Oberwolfach.IntervalCycleWeightTransfer

@[expose] public section

/-! The exact capacity weights are restricted on the fixed tuple space. The
loss at a fixed arc is bounded by C c²(2b+1)/n; retained weights do not change. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem cyclic_successor_ne_self (c : ℕ) (hc : 2≤c) (i : Fin c) : finRotate c i≠i := by
  intro he
  have hh := congrArg Fin.val he
  rw [finRotate_val_if] at hh
  split_ifs at hh <;> omega

theorem separated_capacity_edge_bounds {c : ℕ} (hc : 3≤c)
    {V : Type*} [Fintype V] [Nonempty V]
    (π : Equiv.Perm V) (b : ℕ) (a : Fin c → V → V → ℝ)
    (w : (Fin c → V) → ℝ) (hw : ∀ v,0≤w v)
    (he : ∀ i x y,(∑ v,if v i=x ∧ v (finRotate c i)=y then w v else 0)=a i x y)
    (C : ℝ) (hC : 0≤C)
    (hu : ∀ v,w v≤C/(Fintype.card V : ℝ)^(c-2))
    (i : Fin c) (x y : V) (hxy : ¬PermutationClose π b x y) :
    a i x y-(c:ℝ)^2*(2*b+1)*C/Fintype.card V ≤
      (∑ v,if v i=x ∧ v (finRotate c i)=y then separatedWeight π b w v else 0) ∧
    (∑ v,if v i=x ∧ v (finRotate c i)=y then separatedWeight π b w v else 0)≤a i x y := by
  have hh := separatedWeight_two_positions π b (by simpa using hc)
    i (finRotate c i) (Ne.symm (cyclic_successor_ne_self c (by omega) i)) x y hxy w hw C hC
    (by simpa using hu)
  simpa only [Fintype.card_fin,he] using hh

theorem separated_capacity_support {c : ℕ} {V : Type*} [Fintype V]
    (π : Equiv.Perm V) (b : ℕ) (a : Fin c → V → V → ℝ) (ha : ∀ i x y,0≤a i x y)
    (w : (Fin c → V) → ℝ) (hw : ∀ v,0≤w v)
    (he : ∀ i x y,(∑ v,if v i=x ∧ v (finRotate c i)=y then w v else 0)=a i x y)
    (v : Fin c → V) (hv : 0<separatedWeight π b w v) :
    PermutationSeparated π b v ∧ Function.Injective v ∧ ∀ i,0<a i (v i) (v (finRotate c i)) := by
  have hs : PermutationSeparated π b v := by
    by_contra h
    simp only [separatedWeight,h,ite_false] at hv
    exact (lt_irrefl 0 hv)
  refine ⟨hs,permutationSeparated_injective π b v hs,?_⟩
  intro i
  by_contra h
  have hz := cycleWeight_zero_at_zero_capacity a w hw he v i (le_antisymm (not_lt.mp h) (ha _ _ _))
  rw [separatedWeight_retained π b w v hs,hz] at hv
  exact (lt_irrefl 0 hv)

end Oberwolfach
