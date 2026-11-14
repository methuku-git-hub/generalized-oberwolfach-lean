module

public import Oberwolfach.LongPreparationIneligibleGraph
public import Oberwolfach.GreedyGraphCandidates
public import Oberwolfach.RootComparisonHosts

@[expose] public section
/-! Degree and edge counts for the required graph after the physical
containment in the unassigned, unused, and ineligible graphs is established. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem long_preparation_bad_graph_bounds
    (P Bad Unused Unassigned:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V)
    (a b:ℝ) (ha:0≤a) (hb:0≤b)
    (hA:∀v∈I,(Unassigned.degree v:ℝ)≤a)
    (hB:∀v∈I,(Unused.degree v:ℝ)≤b)
    (hSub:Bad≤(spanningRestriction Unassigned I ⊔ spanningRestriction Unused I) ⊔
      longPreparationIneligibleGraph P π d):
    (∀v,(Bad.degree v:ℝ)≤a+b+(6*d+2:ℕ)) ∧
    2*(Bad.edgeFinset.card:ℝ)≤I.card*(a+b)+(6*d+2:ℕ)*Fintype.card V:=by
  let A:=spanningRestriction Unassigned I
  let B:=spanningRestriction Unused I
  let F:=longPreparationIneligibleGraph P π d
  have hA' (v:V):(A.degree v:ℝ)≤ if v∈I then a else 0:=by
    by_cases hv:v∈I
    · simp only [hv,ite_true]
      exact spanningRestriction_degree_bound Unassigned I a ha hA v
    · simp only [hv,ite_false]
      have hz:A.degree v=0:=by
        rw [← SimpleGraph.card_neighborFinset_eq_degree,Finset.card_eq_zero]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro w hw
        have hh:=(spanningRestriction_adj Unassigned I v w).mp (((spanningRestriction Unassigned I).mem_neighborFinset v w).mp hw)
        exact hv hh.2.1
      simp [hz]
  have hB' (v:V):(B.degree v:ℝ)≤ if v∈I then b else 0:=by
    by_cases hv:v∈I
    · simp only [hv,ite_true]
      exact spanningRestriction_degree_bound Unused I b hb hB v
    · simp only [hv,ite_false]
      have hz:B.degree v=0:=by
        rw [← SimpleGraph.card_neighborFinset_eq_degree,Finset.card_eq_zero]
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro w hw
        have hh:=(spanningRestriction_adj Unused I v w).mp (((spanningRestriction Unused I).mem_neighborFinset v w).mp hw)
        exact hv hh.2.1
      simp [hz]
  have hf (v:V):(F.degree v:ℝ)≤(6*d+2:ℕ):=by exact_mod_cast long_preparation_ineligible_degree P π d v
  have hv (v:V):(Bad.degree v:ℝ)≤(if v∈I then a+b else 0)+(6*d+2:ℕ):=by
    have hdeg:(Bad.degree v:ℝ)≤((A⊔B⊔F).degree v:ℝ):=by exact_mod_cast SimpleGraph.degree_le_of_le hSub
    have hs1:(((A⊔B⊔F).degree v):ℝ)≤((A⊔B).degree v:ℝ)+F.degree v:=by
      have hn: (A⊔B⊔F).degree v≤(A⊔B).degree v+F.degree v:=by
        convert graph_degree_sup_le (A⊔B) F v using 1 <;> congr!
      exact_mod_cast hn
    have hs2:(((A⊔B).degree v):ℝ)≤(A.degree v:ℝ)+B.degree v:=by
      have hn: (A⊔B).degree v≤A.degree v+B.degree v:=by
        convert graph_degree_sup_le A B v using 1 <;> congr!
      exact_mod_cast hn
    have hAv:=hA' v
    have hBv:=hB' v
    by_cases h:v∈I <;> simp only [h,ite_true,ite_false] at hAv hBv ⊢ <;> linarith [hf v]
  constructor
  · intro v
    have hh:=hv v
    by_cases h:v∈I <;> simp only [h,ite_true,ite_false] at hh <;> linarith
  · have hsum:∑v:V,(Bad.degree v:ℝ)≤∑v:V,((if v∈I then a+b else 0)+(6*d+2:ℕ)):=
      Finset.sum_le_sum (fun v _=>hv v)
    have he:∑v:V,(Bad.degree v:ℝ)=2*(Bad.edgeFinset.card:ℝ):=by
      rw [← Nat.cast_sum,Bad.sum_degrees_eq_twice_card_edges]
      push_cast
      ring
    rw [he] at hsum
    simp only [Finset.sum_add_distrib,Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,
      Finset.card_univ,nsmul_eq_mul] at hsum
    nlinarith [hsum]
end Oberwolfach
