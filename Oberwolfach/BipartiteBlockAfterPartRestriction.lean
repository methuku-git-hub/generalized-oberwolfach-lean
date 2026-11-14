module

public import Oberwolfach.BipartiteBlockAfterDeletion

@[expose] public section

/-! Restrict the actual two vertex classes and then delete actual edges.
The lost vertices and edges are counted directly, with no sampling factor
and no new probability event. Large-cut lower bounds survive restriction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_filter_card_le_restriction_plus_loss {X:Type} [DecidableEq X]
    (A A':Finset X) (p:X→Prop):
    (A.filter p).card≤(A'.filter p).card+(A\A').card:=by
  have hs:A.filter p⊆A'.filter p∪(A\A'):=by
    intro x hx
    obtain ⟨hx,hp⟩:=Finset.mem_filter.mp hx
    by_cases hx':x∈A'
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx',hp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx,hx'⟩)
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

variable {X Y:Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem bipartite_block_after_part_restriction
    (E:X→Y→Prop) (A A':Finset X) (B B':Finset Y) (hA:A'⊆A) (hB:B'⊆B)
    (d tau lam loss:ℝ)
    (H:BipartiteBlockBounds E (fun x=>x∈A) (fun y=>y∈B) (d+loss) tau lam)
    (hLA:((A\A').card:ℝ)≤loss) (hLB:((B\B').card:ℝ)≤loss):
    BipartiteBlockBounds E (fun x=>x∈A') (fun y=>y∈B') d tau lam:=by
  constructor
  · intro x hx
    have hold:=H.row x (hA hx)
    have hloss:((B.filter (E x)).card:ℝ)≤(B'.filter (E x)).card+(B\B').card:=by
      exact_mod_cast finite_filter_card_le_restriction_plus_loss B B' (E x)
    simp only [←Finset.filter_filter,Finset.filter_mem_eq_inter,Finset.univ_inter] at hold ⊢
    linarith only [hold,hloss,hLB]
  · intro y hy
    have hold:=H.col y (hB hy)
    have hloss:((A.filter (fun x=>E x y)).card:ℝ)≤(A'.filter (fun x=>E x y)).card+(A\A').card:=by
      exact_mod_cast finite_filter_card_le_restriction_plus_loss A A' (fun x=>E x y)
    simp only [←Finset.filter_filter,Finset.filter_mem_eq_inter,Finset.univ_inter] at hold ⊢
    linarith only [hold,hloss,hLA]
  · intro S T hS hT hs ht
    exact H.cut S T (fun x hx=>hA (hS x hx)) (fun y hy=>hB (hT y hy)) hs ht

theorem bipartite_block_after_part_and_edge_deletion
    (E J:X→Y→Prop) (A A':Finset X) (B B':Finset Y) (hA:A'⊆A) (hB:B'⊆B)
    (d tau lam partLoss edgeLoss:ℝ) (hlam:0≤lam)
    (H:BipartiteBlockBounds E (fun x=>x∈A) (fun y=>y∈B) (d+edgeLoss+partLoss) tau (2*lam))
    (hLA:((A\A').card:ℝ)≤partLoss) (hLB:((B\B').card:ℝ)≤partLoss)
    (hrow:∀ x,((Finset.univ.filter (J x)).card:ℝ)≤edgeLoss)
    (hcol:∀ y,((Finset.univ.filter (fun x=>J x y)).card:ℝ)≤edgeLoss)
    (hcut:edgeLoss≤lam*tau):
    BipartiteBlockBounds (fun x y=>E x y∧¬J x y) (fun x=>x∈A') (fun y=>y∈B') d tau lam:=
  bipartite_block_after_deletion E J _ _ d tau lam edgeLoss hlam
    (bipartite_block_after_part_restriction E A A' B B' hA hB (d+edgeLoss) tau (2*lam) partLoss H hLA hLB)
    hrow hcol hcut

end Oberwolfach
