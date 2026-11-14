module

public import Oberwolfach.LongPreparationBadGraphBounds
public import Mathlib.Algebra.Order.Round

@[expose] public section
/-! Convert a degree bound for the bad graph into the ceiling term used in
matching capacity. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem residual_matching_ceiling_bound
    {n:ℕ} (hn:0<n) (G:SimpleGraph (Fin n)) (α b:ℝ) (hα:0<α) (hb:0≤b)
    (hdegree:∀v,(G.degree v:ℝ)≤b*n):
    (⌈4*(G.edgeFinset.card:ℝ)/(α*n)⌉₊:ℝ)<(2*b/α)*n+1:=by
  have hnR:0<(n:ℝ):=by exact_mod_cast hn
  have hsum:∑v:Fin n,(G.degree v:ℝ)≤∑_v:Fin n,b*(n:ℝ):=by
    apply Finset.sum_le_sum
    intro v hv
    exact hdegree v
  have he:(∑v:Fin n,(G.degree v:ℝ))=2*(G.edgeFinset.card:ℝ):=by
    rw [←Nat.cast_sum,G.sum_degrees_eq_twice_card_edges]
    push_cast
    ring
  rw [he] at hsum
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have hnonneg:0≤4*(G.edgeFinset.card:ℝ)/(α*n):=by positivity
  have hceil:=Nat.ceil_lt_add_one hnonneg
  have hbound:4*(G.edgeFinset.card:ℝ)/(α*n)≤(2*b/α)*n:=by
    apply (div_le_iff₀ (by positivity:0<α*(n:ℝ))).2
    have heq:((2*b/α)*(n:ℝ))*(α*n)=2*b*(n:ℝ)^2:=by field_simp
    rw [heq]
    nlinarith
  linarith
end Oberwolfach
