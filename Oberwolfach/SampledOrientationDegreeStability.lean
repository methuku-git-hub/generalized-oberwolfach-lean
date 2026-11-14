module

public import Oberwolfach.RandomOrientation
public import Oberwolfach.Neighbourhoods

@[expose] public section
/-! Changing the physical class graph alters a sampled outdegree by at most
its incident symmetric-difference degree, with the same direction bits. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sampled_orientation_degree_stability
    {V:Type} [Fintype V] [LinearOrder V] (S T:SimpleGraph V) (bits:Sym2 V→Bool) (v:V):
    |((∑w,sampledOrientation S bits v w:ℕ):ℝ)-
      ((∑w,sampledOrientation T bits v w:ℕ):ℝ)|≤
      ((changed (S.neighborFinset v) (T.neighborFinset v)).card:ℝ):=by
  let A:=Finset.univ.filter (fun w=>0<sampledOrientation S bits v w)
  let B:=Finset.univ.filter (fun w=>0<sampledOrientation T bits v w)
  have hcardS:(A.card:ℕ)=∑w,sampledOrientation S bits v w:=by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro w _
    simp only [sampledOrientation]
    split_ifs <;> simp_all
  have hcardT:(B.card:ℕ)=∑w,sampledOrientation T bits v w:=by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro w _
    simp only [sampledOrientation]
    split_ifs <;> simp_all
  have hsub:changed A B⊆changed (S.neighborFinset v) (T.neighborFinset v):=by
    intro w hw
    simp only [changed,Finset.mem_union,Finset.mem_sdiff,SimpleGraph.mem_neighborFinset] at hw ⊢
    simp only [A,B,Finset.mem_filter,Finset.mem_univ,true_and] at hw
    by_cases hs:S.Adj v w <;> by_cases ht:T.Adj v w <;>
      simp [sampledOrientation,hs,ht] at hw ⊢
    all_goals (try split_ifs at hw) <;> simp_all
  have hc:((changed A B).card:ℝ)≤(changed (S.neighborFinset v) (T.neighborFinset v)).card:=by
    exact_mod_cast Finset.card_le_card hsub
  have hh:=card_difference_le_changed A B
  rw [hcardS,hcardT] at hh
  exact hh.trans hc
end Oberwolfach
