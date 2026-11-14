module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Tactic

@[expose] public section
/-! If a graph has no edges inside I, total inner degree is bounded by
the total degree on the complement. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem inner_boundary_total_degree
    {V:Type} [Fintype V] [DecidableEq V] (H:SimpleGraph V) (I:Finset V)
    (hinner:∀v∈I,∀w∈I,¬H.Adj v w):
    (∑v∈I,H.degree v)≤∑w∈Finset.univ\I,H.degree w :=by
  have hdeg:∀v,H.degree v=∑w:V,if H.Adj v w then (1:ℕ) else 0:=by
    intro v
    rw [←SimpleGraph.card_neighborFinset_eq_degree]
    rw [SimpleGraph.neighborFinset_eq_filter]
    exact Finset.card_filter _ _
  have hrestrict:∀v∈I,(∑w:V,if H.Adj v w then (1:ℕ) else 0)=
      ∑w∈Finset.univ\I,if H.Adj v w then (1:ℕ) else 0:=by
    intro v hv
    symm
    apply Finset.sum_subset (Finset.sdiff_subset)
    intro w hw hnot
    have hwI:w∈I:=by simpa only [Finset.mem_sdiff,Finset.mem_univ,true_and,not_not] using hnot
    simp [hinner v hv w hwI]
  calc
    _ = ∑v∈I,∑w∈Finset.univ\I,if H.Adj v w then (1:ℕ) else 0:=by
      apply Finset.sum_congr rfl
      intro v hv
      rw [hdeg v,hrestrict v hv]
    _ = ∑w∈Finset.univ\I,∑v∈I,if H.Adj w v then (1:ℕ) else 0:=by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w hw
      apply Finset.sum_congr rfl
      intro v hv
      have hh:H.Adj v w↔H.Adj w v:=H.adj_comm v w
      simp only [hh]
    _ ≤ ∑w∈Finset.univ\I,H.degree w:=by
      apply Finset.sum_le_sum
      intro w hw
      rw [hdeg w]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ I)
theorem inner_boundary_total_degree_bound
    {V:Type} [Fintype V] [DecidableEq V] (H:SimpleGraph V) (I:Finset V) (L:ℝ)
    (hinner:∀v∈I,∀w∈I,¬H.Adj v w) (hL:0≤L)
    (hout:∀v,v∉I→(H.degree v:ℝ)≤L):
    (∑v∈I,(H.degree v:ℝ))≤Fintype.card V*L :=by
  have hn:=inner_boundary_total_degree H I hinner
  have hc:(∑v∈I,(H.degree v:ℝ))≤∑v∈Finset.univ\I,(H.degree v:ℝ):=by exact_mod_cast hn
  have ho:(∑v∈Finset.univ\I,(H.degree v:ℝ))≤∑_v∈Finset.univ\I,L:=by
    apply Finset.sum_le_sum
    intro v hv
    exact hout v (Finset.mem_sdiff.mp hv).2
  have hcard:((Finset.univ\I).card:ℝ)≤Fintype.card V:=by exact_mod_cast Finset.card_le_univ (Finset.univ\I)
  have hm:=mul_le_mul_of_nonneg_right hcard hL
  have ho':(∑v∈Finset.univ\I,(H.degree v:ℝ))≤((Finset.univ\I).card:ℝ)*L:=by
    simpa only [Finset.sum_const, nsmul_eq_mul] using ho
  exact hc.trans (ho'.trans hm)
end Oberwolfach
