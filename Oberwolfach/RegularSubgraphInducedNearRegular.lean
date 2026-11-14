module

public import Oberwolfach.RegularInducedNearRegular

@[expose] public section
/-! Bounded-degree edge deletions add their actual loss to the error from
restricting a regular host to a large vertex set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem regular_subgraph_induced_near_centre {V:Type} [Fintype V] [DecidableEq V]
    (G Q:SimpleGraph V) (D:ℕ) (hreg:G.IsRegularOfDegree D) (hQ:Q≤G)
    (B:Finset V) (t:ℝ) (ht:∀ v,((G\Q).degree v:ℝ)≤t) (v:(B:Set V)):
    |(((Q.induce (B:Set V)).degree v):ℝ)-((D:ℝ)/Fintype.card V)*B.card|≤
      (Fintype.card V-B.card:ℕ)+t:=by
  have hregnear:=abs_le.mp (regular_induced_degree_near_centre G D hreg B v)
  have hsub:Q.neighborFinset v.val∩B⊆G.neighborFinset v.val∩B:=by
    intro w hw
    have hh:Q.Adj v.val w:=by simpa using (Finset.mem_inter.mp hw).1
    exact Finset.mem_inter.mpr ⟨by simpa using hQ hh,(Finset.mem_inter.mp hw).2⟩
  have hupper:((Q.neighborFinset v.val∩B).card:ℝ)≤(G.neighborFinset v.val∩B).card:=by
    exact_mod_cast Finset.card_le_card hsub
  have hsub':G.neighborFinset v.val∩B⊆(Q.neighborFinset v.val∩B)∪(G\Q).neighborFinset v.val:=by
    intro w hw
    have hg:G.Adj v.val w:=by simpa using (Finset.mem_inter.mp hw).1
    by_cases hq:Q.Adj v.val w
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨by simpa using hq,(Finset.mem_inter.mp hw).2⟩)
    · exact Finset.mem_union_right _ (by simpa using (show (G\Q).Adj v.val w from ⟨hg,hq⟩))
  have hlower:((G.neighborFinset v.val∩B).card:ℝ)≤((Q.neighborFinset v.val∩B).card:ℝ)+t:=by
    have hh:=(Finset.card_le_card hsub').trans (Finset.card_union_le _ _)
    rw [SimpleGraph.card_neighborFinset_eq_degree] at hh
    have hh':((G.neighborFinset v.val∩B).card:ℝ)≤(Q.neighborFinset v.val∩B).card+((G\Q).degree v.val:ℝ):=by exact_mod_cast hh
    linarith [ht v.val]
  rw [graph_induced_degree_as_intersection] at hregnear ⊢
  apply abs_le.mpr
  constructor <;> linarith [ht v.val]
end Oberwolfach
