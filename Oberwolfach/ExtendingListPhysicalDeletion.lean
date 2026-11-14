module

public import Oberwolfach.ExtendingListStability
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section
/-! A sparse undirected physical deletion removes at most its degree from
both directed neighbourhoods, and hence at most twice that from common tests. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem extending_list_after_physical_deletion
    {V:Type} [Fintype V] [DecidableEq V] (D:V→V→Prop) (Del:SimpleGraph V)
    (L:Finset V) (β lam r:ℝ) (hlam:0≤lam) (hr:0≤r)
    (hDel:∀x,(Del.degree x:ℝ)≤r)
    (hbudget:lam*Fintype.card V+2*r≤β*Fintype.card V)
    (hext:IsExtendingList D L β):
    IsExtendingList (fun x y=>D x y ∧ ¬Del.Adj x y) L lam:=by
  let D':=fun x y=>D x y ∧ ¬Del.Adj x y
  apply extending_list_after_neighbourhood_changes D D' L L β lam r 0 hlam hr (by norm_num) ?_ ?_ ?_ ?_ hext
  · simp
  · intro x
    have hsub:directedOutNeighbours D x\directedOutNeighbours D' x⊆Del.neighborFinset x:=by
      intro y hy
      simp only [Finset.mem_sdiff,directedOutNeighbours,Finset.mem_filter,Finset.mem_univ,true_and] at hy
      simp only [SimpleGraph.mem_neighborFinset]
      dsimp [D'] at hy
      tauto
    have hc:=Finset.card_le_card hsub
    have hc':((directedOutNeighbours D x\directedOutNeighbours D' x).card:ℝ)≤Del.degree x:=by
      exact_mod_cast (by simpa using hc)
    exact hc'.trans (hDel x)
  · intro x
    have hsub:directedInNeighbours D x\directedInNeighbours D' x⊆Del.neighborFinset x:=by
      intro y hy
      simp only [Finset.mem_sdiff,directedInNeighbours,Finset.mem_filter,Finset.mem_univ,true_and] at hy
      simp only [SimpleGraph.mem_neighborFinset]
      dsimp [D'] at hy
      have h:Del.Adj y x:=by tauto
      exact h.symm
    have hc:=Finset.card_le_card hsub
    have hc':((directedInNeighbours D x\directedInNeighbours D' x).card:ℝ)≤Del.degree x:=by
      exact_mod_cast (by simpa using hc)
    exact hc'.trans (hDel x)
  · simpa using hbudget
end Oberwolfach
