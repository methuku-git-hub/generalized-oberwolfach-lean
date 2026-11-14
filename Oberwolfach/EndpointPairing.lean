module

public import Oberwolfach.NeighbourPairDomains
public import Oberwolfach.GraphSelectionDegrees

@[expose] public section

/-! The actual two-edge assignment at a boundary root. Each hub receives
two distinct row vertices, and each row vertex is used exactly once. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

structure EndpointPairing (G F:SimpleGraph V) (A B:Finset V) where
  disjoint_parts : Disjoint A B
  left : B ↪ A
  right : B ↪ A
  adjacent : ∀ u,G.Adj (left u).val u.val ∧ G.Adj (right u).val u.val
  avoid : ∀ u,¬F.Adj (left u).val (right u).val
  disjoint_ranges : Disjoint (Set.range left) (Set.range right)
  cover : ∀ v:A,(∃ u,left u=v) ∨ ∃ u,right u=v

theorem endpoint_pairing_of_degree_cuts (c:ℝ) (hc:0<c) (b:ℕ):
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [DecidableEq V] (G F:SimpleGraph V) (A B:Finset V),
      N≤B.card→A.card=2*B.card→Disjoint A B→
      (∀ v,F.degree v≤b)→
      (∀ v∈A,c*B.card≤((B∩G.neighborFinset v).card:ℝ))→
      (∀ u∈B,c*A.card≤((A∩G.neighborFinset u).card:ℝ))→
      (∀ S⊆A,∀ T⊆B,c/16*B.card≤(S.card:ℝ)→c/16*B.card≤(T.card:ℝ)→
        c*S.card*T.card≤(bipartiteMatrixCut (fun v w=>if G.Adj v w then 1 else 0) S T:ℝ))→
      Nonempty (EndpointPairing G F A B):=by
  obtain ⟨N,hN⟩:=ordinary_neighbour_pair_assignment c hc b
  refine ⟨N,?_⟩
  intro V _ _ G F A B hn hAB hdis hF hrow hcol hcut
  let eA:A↪V:=⟨Subtype.val,Subtype.val_injective⟩
  let eB:B↪V:=⟨Subtype.val,Subtype.val_injective⟩
  have hrow' (v:A):c*B.card≤((Finset.univ.filter (fun u:B=>G.Adj v.val u.val)).card:ℝ):=by
    rw [finite_domain_predicate_card]
    have he:B.filter (G.Adj v.val)=B∩G.neighborFinset v.val:=by ext u;simp
    rw [he];exact hrow v.val v.property
  have hcol' (u:B):2*c*B.card≤((Finset.univ.filter (fun v:A=>G.Adj v.val u.val)).card:ℝ):=by
    rw [finite_domain_predicate_card A (fun v=>G.Adj v u.val)]
    have he:A.filter (fun v=>G.Adj v u.val)=A∩G.neighborFinset u.val:=by
      ext v;simp only [Finset.mem_filter,Finset.mem_inter,SimpleGraph.mem_neighborFinset,G.adj_comm]
    rw [he]
    have hh:=hcol u.val u.property
    rw [hAB,Nat.cast_mul,Nat.cast_ofNat] at hh
    nlinarith only [hh]
  have hcut' (S:Finset A) (T:Finset B)
      (hS:c/16*B.card≤(S.card:ℝ)) (hT:c/16*B.card≤(T.card:ℝ)):
      c*S.card*T.card≤(bipartiteMatrixCut (fun v:A=>fun u:B=>if G.Adj v.val u.val then 1 else 0) S T:ℝ):=by
    have hh:=hcut (S.map eA) (by rintro v hv;obtain ⟨x,hx,rfl⟩:=Finset.mem_map.mp hv;exact x.property)
      (T.map eB) (by rintro u hu;obtain ⟨x,hx,rfl⟩:=Finset.mem_map.mp hu;exact x.property)
      (by simpa only [Finset.card_map] using hS) (by simpa only [Finset.card_map] using hT)
    simpa only [Finset.card_map,bipartiteMatrixCut,Finset.sum_map,eA,eB,Function.Embedding.coeFn_mk] using hh
  obtain ⟨v,w,hadj,hranges,hcover⟩:=hN A B B.card hn
    (by simpa only [Fintype.card_coe] using hAB) (Fintype.card_coe B)
    (fun v:A=>fun u:B=>G.Adj v.val u.val) (F.comap Subtype.val)
    hrow' hcol' (fun v=>(embedding_comap_degree_le eA F v).trans (hF v.val)) hcut'
  exact ⟨⟨hdis,v,w,fun u=>⟨(hadj u).1,(hadj u).2.1⟩,fun u=>(hadj u).2.2,hranges,hcover⟩⟩

namespace EndpointPairing
variable {G F:SimpleGraph V} {A B:Finset V}

def graph (P:EndpointPairing G F A B):SimpleGraph V where
  Adj x y := ∃ u:B,(x=u.val ∧ (y=(P.left u).val ∨ y=(P.right u).val)) ∨
    (y=u.val ∧ (x=(P.left u).val ∨ x=(P.right u).val))
  symm := ⟨by
    intro x y
    rintro ⟨u,h|h⟩
    · exact ⟨u,Or.inr h⟩
    · exact ⟨u,Or.inl h⟩⟩
  loopless := ⟨by
    intro x
    have hnot (u:B):u.val∉A:=fun hu=>Finset.disjoint_left.mp P.disjoint_parts hu u.property
    rintro ⟨u,⟨h,h'|h'⟩|⟨h,h'|h'⟩⟩
    · apply hnot u;rw [←h,h'];exact (P.left u).property
    · apply hnot u;rw [←h,h'];exact (P.right u).property
    · apply hnot u;rw [←h,h'];exact (P.left u).property
    · apply hnot u;rw [←h,h'];exact (P.right u).property⟩

theorem left_ne_right (P:EndpointPairing G F A B) (u w:B):
    (P.left u).val≠(P.right w).val:=by
  intro h
  exact Set.disjoint_left.mp P.disjoint_ranges ⟨u,rfl⟩ ⟨w,Subtype.ext h.symm⟩

theorem graph_le (P:EndpointPairing G F A B):P.graph≤spanningRestriction G (A∪B):=by
  intro x y hxy
  obtain ⟨u,⟨rfl,rfl|rfl⟩|⟨rfl,rfl|rfl⟩⟩:=hxy
  · exact (spanningRestriction_adj _ _ _ _).mpr ⟨(P.adjacent u).1.symm,
      Finset.mem_union_right _ u.property,Finset.mem_union_left _ (P.left u).property⟩
  · exact (spanningRestriction_adj _ _ _ _).mpr ⟨(P.adjacent u).2.symm,
      Finset.mem_union_right _ u.property,Finset.mem_union_left _ (P.right u).property⟩
  · exact (spanningRestriction_adj _ _ _ _).mpr ⟨(P.adjacent u).1,
      Finset.mem_union_left _ (P.left u).property,Finset.mem_union_right _ u.property⟩
  · exact (spanningRestriction_adj _ _ _ _).mpr ⟨(P.adjacent u).2,
      Finset.mem_union_left _ (P.right u).property,Finset.mem_union_right _ u.property⟩

end EndpointPairing
end Oberwolfach
