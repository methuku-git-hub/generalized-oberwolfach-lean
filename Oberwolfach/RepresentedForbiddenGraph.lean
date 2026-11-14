module

public import Oberwolfach.ForbiddenGraphPairs
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

/-! Pull back forbidden physical edges to pairs of distinct auxiliary
labels. Each label has two injective representations (itself and, for marked
heads, its successor). The maximum degree increases by at most four. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W:Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

def representedForbiddenGraph (F:SimpleGraph W) (f g:V↪W):SimpleGraph V where
  Adj x y:=x≠y ∧ (F.Adj (f x) (f y) ∨ F.Adj (f x) (g y) ∨
    F.Adj (g x) (f y) ∨ F.Adj (g x) (g y))
  symm:=⟨by
    intro x y h
    refine ⟨h.1.symm,?_⟩
    rcases h.2 with h|h|h|h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr (Or.inl h.symm))
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr (Or.inr h.symm))⟩
  loopless:=⟨by intro x h;exact h.1 rfl⟩

theorem injective_graph_neighbour_filter_card (F:SimpleGraph W) (e:V↪W) (w:W):
    (Finset.univ.filter (fun v=>F.Adj w (e v))).card≤F.degree w:=by
  have hs:(Finset.univ.filter (fun v=>F.Adj w (e v))).image e⊆F.neighborFinset w:=by
    intro v hv
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hv
    exact (SimpleGraph.mem_neighborFinset _ _ _).mpr (Finset.mem_filter.mp hx).2
  have hh:=Finset.card_le_card hs
  simpa only [Finset.card_image_of_injective _ e.injective,SimpleGraph.card_neighborFinset_eq_degree] using hh

theorem representedForbiddenGraph_degree (F:SimpleGraph W) (f g:V↪W) (v:V):
    (representedForbiddenGraph F f g).degree v≤2*F.degree (f v)+2*F.degree (g v):=by
  let A:=Finset.univ.filter (fun y=>F.Adj (f v) (f y))
  let B:=Finset.univ.filter (fun y=>F.Adj (f v) (g y))
  let C:=Finset.univ.filter (fun y=>F.Adj (g v) (f y))
  let D:=Finset.univ.filter (fun y=>F.Adj (g v) (g y))
  have hs:(representedForbiddenGraph F f g).neighborFinset v⊆(A∪B)∪(C∪D):=by
    intro y hy
    have hh:=(SimpleGraph.mem_neighborFinset _ _ _).mp hy
    change v≠y ∧ (F.Adj (f v) (f y) ∨ F.Adj (f v) (g y) ∨
      F.Adj (g v) (f y) ∨ F.Adj (g v) (g y)) at hh
    simp only [Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,A,B,C,D]
    tauto
  have hcard:=Finset.card_le_card hs
  have hab:=Finset.card_union_le A B
  have hcd:=Finset.card_union_le C D
  have ht:=Finset.card_union_le (A∪B) (C∪D)
  have ha:=injective_graph_neighbour_filter_card F f (f v)
  have hb:=injective_graph_neighbour_filter_card F g (f v)
  have hc:=injective_graph_neighbour_filter_card F f (g v)
  have hd:=injective_graph_neighbour_filter_card F g (g v)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hcard
  change A.card≤F.degree (f v) at ha
  change B.card≤F.degree (f v) at hb
  change C.card≤F.degree (g v) at hc
  change D.card≤F.degree (g v) at hd
  omega

theorem representedForbiddenGraph_degree_bound (F:SimpleGraph W) (f g:V↪W) (d:ℝ)
    (hd:∀ v,(F.degree v:ℝ)≤d) (v:V):
    ((representedForbiddenGraph F f g).degree v:ℝ)≤4*d:=by
  have hh:((representedForbiddenGraph F f g).degree v:ℝ)≤
      2*(F.degree (f v):ℝ)+2*(F.degree (g v):ℝ):=by
    exact_mod_cast representedForbiddenGraph_degree F f g v
  linarith only [hh,hd (f v),hd (g v)]

theorem representedForbiddenGraph_avoidance (F:SimpleGraph W) (f g:V↪W) (A:Finset V)
    (hA:∀ x∈A,∀ y∈A,¬(representedForbiddenGraph F f g).Adj x y)
    {x y:V} (hx:x∈A) (hy:y∈A) (hne:x≠y):
    ¬F.Adj (f x) (f y) ∧ ¬F.Adj (f x) (g y) ∧
      ¬F.Adj (g x) (f y) ∧ ¬F.Adj (g x) (g y):=by
  have hh:=hA x hx y hy
  change ¬(x≠y ∧ (F.Adj (f x) (f y) ∨ F.Adj (f x) (g y) ∨
    F.Adj (g x) (f y) ∨ F.Adj (g x) (g y))) at hh
  tauto

end Oberwolfach
