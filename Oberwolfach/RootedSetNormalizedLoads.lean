module

public import Oberwolfach.RootedSetIncidence
public import Oberwolfach.RootOmittedInducedEdges

@[expose] public section

/-! The normalized family of root-omitted induced-edge patterns has total
weight at most one and edge incidence at most 1/n. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] {k : ℕ}

theorem fixedSetFamily_normalized_total (S : I → FixedSubset V k) (hinj : Function.Injective S)
    (x y : V) (hxy : x≠y) (hk : 2≤k) (hn : 0<Fintype.card V)
    (hroot : ∀ i,x∈(S i).val ∧ y∈(S i).val) :
    (∑ _ : I,1/(Fintype.card V:ℝ)^(k-2))≤1 := by
  have hpos : (0:ℝ)<(Fintype.card V:ℝ)^(k-2) := by positivity
  have hh := fixedSetFamily_total S hinj x y hxy hk hroot
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one_div]
  exact (div_le_one hpos).mpr hh


theorem fixedSetFamily_normalized_edge_load (P : SimpleGraph V)
    (S : I → FixedSubset V k) (hinj : Function.Injective S)
    (x y : V) (hxy : x≠y) (hk : 4≤k) (hn : 0<Fintype.card V)
    (hroot : ∀ i,x∈(S i).val ∧ y∈(S i).val) (e : Sym2 V) :
    (∑ i,if e∈rootOmittedInducedEdges P (S i).val s(x,y)
      then 1/(Fintype.card V:ℝ)^(k-2) else 0)≤1/Fintype.card V := by
  induction e using Sym2.ind with
  | _ z t=>
    by_cases hz : P.Adj z t
    · by_cases he : s(z,t)=s(x,y)
      · simp only [mem_rootOmittedInducedEdges,he,ne_eq,not_true_eq_false,false_and,ite_false,Finset.sum_const_zero]
        positivity
      · have hh := fixedSetFamily_distinct_edge_count S hinj x y hxy hk hn hroot z t hz.ne (Ne.symm he)
        have hterm (i : I) :
            (if s(z,t)∈rootOmittedInducedEdges P (S i).val s(x,y)
              then 1/(Fintype.card V:ℝ)^(k-2) else 0)=
            (if z∈(S i).val ∧ t∈(S i).val then (1:ℝ) else 0)/(Fintype.card V:ℝ)^(k-2) := by
          simp only [mem_rootOmittedInducedEdges,ne_eq,he,not_false_eq_true,hz,true_and]
          split_ifs <;> simp
        simp_rw [hterm]
        rw [← Finset.sum_div]
        calc
          _ ≤ (Fintype.card V:ℝ)^(k-3)/(Fintype.card V:ℝ)^(k-2) :=
            div_le_div_of_nonneg_right hh (by positivity)
          _ = 1/Fintype.card V := by
            have heq : k-2=k-3+1 := by omega
            rw [heq,pow_succ]
            have hnp : (Fintype.card V:ℝ)≠0 := by positivity
            field_simp
    · simp only [mem_rootOmittedInducedEdges,hz,false_and,and_false,ite_false,Finset.sum_const_zero]
      positivity

end Oberwolfach
