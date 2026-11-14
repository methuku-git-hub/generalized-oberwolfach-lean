module

public import Oberwolfach.SubsetMean
public import Mathlib.Data.Nat.Choose.Cast

@[expose] public section

/-! Exact first and centred second moments for uniform fixed-size root
sets. These identities supply the signed vertex-demand correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_weighted_indicators {Ω V : Type*} [Fintype Ω] [Fintype V]
    (μ : FiniteLaw Ω) (P : V → Ω → Prop) (y : V → ℝ) :
    μ.expectation (fun ω => ∑ v,if P v ω then y v else 0)=
      ∑ v,y v*μ.probability (P v) := by
  unfold FiniteLaw.expectation FiniteLaw.probability
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : P v ω <;> simp [h,mul_comm]

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ} [Nonempty (FixedSubset V r)]

theorem fixedSubset_weighted_mean (hr : r ≤ Fintype.card V) (y : V → ℝ) :
    (FiniteLaw.uniform (FixedSubset V r)).expectation (fun S => ∑ v∈S.val,y v)=
      (r:ℝ)/Fintype.card V*(∑ v,y v) := by
  have heq (S : FixedSubset V r) : (∑ v∈S.val,y v)=∑ v,if v∈S.val then y v else 0 := by simp
  simp_rw [heq]
  calc
    _ = ∑ v,y v*(FiniteLaw.uniform (FixedSubset V r)).probability (fun S => v∈S.val) := by
      convert finiteLaw_weighted_indicators (FiniteLaw.uniform (FixedSubset V r)) (fun v S => v∈S.val) y using 1 <;> congr!
    _ = _ := by
      simp_rw [fixedSubset_vertex_probability hr]
      rw [← Finset.sum_mul,mul_comm]

theorem fixedSubset_distinct_pair_probability_formula (hr : r ≤ Fintype.card V) (u v : V) (huv : u≠v) :
    (FiniteLaw.uniform (FixedSubset V r)).probability (fun S => u∈S.val ∧ v∈S.val)=
      (r:ℝ)*(r-1)/((Fintype.card V:ℝ)*(Fintype.card V-1)) := by
  have hh := fixedSubset_joint_inclusion hr {u,v}
  rw [Finset.card_pair huv,Nat.cast_choose_two,Nat.cast_choose_two] at hh
  simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff] at hh
  rw [hh]
  exact div_div_div_cancel_right₀ (by norm_num : (2:ℝ)≠0) _ _

theorem fixedSubset_centred_moment (hr : r ≤ Fintype.card V) (hn : 2 ≤ Fintype.card V)
    (y : V → ℝ) (hy : ∑ v,y v=0) (v : V) :
    (FiniteLaw.uniform (FixedSubset V r)).expectation
      (fun S => if v∈S.val then (∑ u∈S.val,y u) else 0)=
      (r:ℝ)*(Fintype.card V-r)/((Fintype.card V:ℝ)*(Fintype.card V-1))*y v := by
  let μ := FiniteLaw.uniform (FixedSubset V r)
  let a : ℝ := r/Fintype.card V
  let b : ℝ := (r:ℝ)*(r-1)/((Fintype.card V:ℝ)*(Fintype.card V-1))
  have heq (S : FixedSubset V r) :
      (if v∈S.val then (∑ u∈S.val,y u) else 0)=
      ∑ u,if v∈S.val ∧ u∈S.val then y u else 0 := by
    by_cases hv : v∈S.val <;> simp [hv]
  simp_rw [heq]
  calc
    _ = ∑ u,y u*μ.probability (fun S => v∈S.val ∧ u∈S.val) := by
      convert finiteLaw_weighted_indicators μ (fun u S => v∈S.val ∧ u∈S.val) y using 1 <;> congr!
    _ = _ := by
      have hi (u : V) : y u*μ.probability (fun S => v∈S.val ∧ u∈S.val)=
          (if u=v then (a-b)*y v else 0)+b*y u := by
        by_cases huv : u=v
        · subst u
          simp only [and_self,fixedSubset_vertex_probability hr,ite_true]
          dsimp [a,μ]
          rw [fixedSubset_vertex_probability hr]
          ring
        · rw [fixedSubset_distinct_pair_probability_formula hr v u (Ne.symm huv)]
          simp only [huv,ite_false,zero_add]
          dsimp [b]
          ring
      change (∑ u,y u*μ.probability (fun S => v∈S.val ∧ u∈S.val))=_
      simp_rw [hi,Finset.sum_add_distrib,← Finset.mul_sum,hy,mul_zero,add_zero]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      have hnR : (1:ℝ)<Fintype.card V := by exact_mod_cast (show 1<Fintype.card V by omega)
      have hn0 : (Fintype.card V:ℝ)≠0 := by linarith
      have hn1 : (Fintype.card V:ℝ)-1≠0 := by linarith
      dsimp [a,b]
      field_simp
      <;> ring

end Oberwolfach
