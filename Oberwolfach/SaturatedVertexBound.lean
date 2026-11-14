module

public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! The greedy embedding can exclude all labels used at least t times:
the number of such labels is bounded by total use divided by t. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem saturated_vertex_count_bound {V:Type} [Fintype V] (f:V→ℕ) (t T:ℝ)
    (ht:0<t) (hused:(∑ v,(f v:ℝ))≤T):
    let S:=Finset.univ.filter (fun v=>(t:ℝ)≤f v);
    t*(S.card:ℝ)≤T := by
  intro S
  have hpoint:∑ v∈S,t≤∑ v∈S,(f v:ℝ):=by
    apply Finset.sum_le_sum
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hsub:(∑ v∈S,(f v:ℝ))≤∑ v,(f v:ℝ):=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun v _ _=>by positivity)
  simp only [Finset.sum_const,nsmul_eq_mul] at hpoint
  nlinarith

theorem saturated_vertex_count_sqrt_bound {V:Type} [Fintype V] (f:V→ℕ) (t T:ℝ)
    (ht:0<t) (hused:(∑ v,(f v:ℝ))≤T) (hscale:T≤t^2):
    ((Finset.univ.filter (fun v=>(t:ℝ)≤f v)).card:ℝ)≤t := by
  have hh:=saturated_vertex_count_bound f t T ht hused
  nlinarith
theorem prescribed_embedding_saturated_vertices {V:Type} [Fintype V] (f:V→ℕ) (δ n:ℝ)
    (hδ:0<δ) (hn:0<n) (hused:(∑ v,(f v:ℝ))≤δ*n^2):
    let t:=Real.sqrt δ*n;
    ((Finset.univ.filter (fun v=>(t:ℝ)≤f v)).card:ℝ)≤t := by
  intro t
  have ht:0<t:=by dsimp [t];positivity
  have heq:t^2=δ*n^2:=by dsimp [t];rw [mul_pow,Real.sq_sqrt hδ.le]
  exact saturated_vertex_count_sqrt_bound f t (δ*n^2) ht hused heq.symm.le
end Oberwolfach
