module

public import Oberwolfach.TriangleTransformerFactors

@[expose] public section
/-! Restricting the neighbourhood domain and deleting a graph of maximum
degree two changes each retained degree by at most the displayed losses. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem induced_bounded_deletion_degrees {V:Type} [Fintype V] [DecidableEq V]
    (G Dgraph:SimpleGraph V) (S A:Finset V) (D η:ℝ) (b:ℕ)
    (hAS:A⊆S) (hbound:(S\A).card≤b)
    (hnear:∀ v,|((G.neighborFinset v∩S).card:ℝ)-D|≤η*S.card)
    (hD:∀ v,Dgraph.degree v≤2) (v:(A:Set V)):
    let Q:=triangleAugmentationGraph G Dgraph A;
    |(((Q.induce (A:Set V)).degree v):ℝ)-D|≤η*S.card+b+2:=by
  intro Q
  have hsub:G.neighborFinset v.val∩A⊆G.neighborFinset v.val∩S:=by
    intro x hx;exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,hAS (Finset.mem_inter.mp hx).2⟩
  have hup:((G.neighborFinset v.val∩A).card:ℝ)≤(G.neighborFinset v.val∩S).card:=by
    exact_mod_cast Finset.card_le_card hsub
  have hsub2:G.neighborFinset v.val∩S⊆(G.neighborFinset v.val∩A)∪(S\A):=by
    intro x hx
    by_cases ha:x∈A
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,ha⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hx).2,ha⟩)
  have hloss:((G.neighborFinset v.val∩S).card:ℝ)≤((G.neighborFinset v.val∩A).card:ℝ)+b:=by
    have hh:=(Finset.card_le_card hsub2).trans (Finset.card_union_le _ _)
    have hh':(G.neighborFinset v.val∩S).card≤(G.neighborFinset v.val∩A).card+b:=by omega
    exact_mod_cast hh'
  have hQ:Q≤G:=fun _ _ h=>h.1
  have hQsub:Q.neighborFinset v.val∩A⊆G.neighborFinset v.val∩A:=by
    intro x hx
    exact Finset.mem_inter.mpr ⟨by
      have hh:Q.Adj v.val x:=by simpa using (Finset.mem_inter.mp hx).1
      simpa using hQ hh,(Finset.mem_inter.mp hx).2⟩
  have hQup:((Q.neighborFinset v.val∩A).card:ℝ)≤(G.neighborFinset v.val∩A).card:=by
    exact_mod_cast Finset.card_le_card hQsub
  have hQlow:((G.neighborFinset v.val∩A).card:ℝ)-2≤(Q.neighborFinset v.val∩A).card:=by
    have hsub3:G.neighborFinset v.val∩A⊆(Q.neighborFinset v.val∩A)∪Dgraph.neighborFinset v.val:=by
      intro x hx
      have hg:G.Adj v.val x:=by simpa using (Finset.mem_inter.mp hx).1
      by_cases hd:Dgraph.Adj v.val x
      · exact Finset.mem_union_right _ (by simpa using hd)
      · apply Finset.mem_union_left
        exact Finset.mem_inter.mpr ⟨by simpa using (show Q.Adj v.val x from ⟨hg,Or.inl v.property,hd⟩),(Finset.mem_inter.mp hx).2⟩
    have hh:=(Finset.card_le_card hsub3).trans (Finset.card_union_le _ _)
    rw [SimpleGraph.card_neighborFinset_eq_degree] at hh
    have hhR:((G.neighborFinset v.val∩A).card:ℝ)≤(Q.neighborFinset v.val∩A).card+(Dgraph.degree v.val:ℝ):=by exact_mod_cast hh
    have hdR:(Dgraph.degree v.val:ℝ)≤2:=by exact_mod_cast hD v.val
    linarith
  have hh:=abs_le.mp (hnear v.val)
  rw [graph_induced_degree_as_intersection]
  apply abs_le.mpr
  constructor <;> linarith
end Oberwolfach
