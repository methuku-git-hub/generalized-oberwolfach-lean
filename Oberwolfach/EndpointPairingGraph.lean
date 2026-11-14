module

public import Oberwolfach.EndpointPairing

@[expose] public section

/-! The selected endpoint pairs form an actual physical graph of maximum
degree two. Both the graph and the original pair assignment are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V] {G F:SimpleGraph V} {A B:Finset V}
namespace EndpointPairing

theorem row_hub_unique (P:EndpointPairing G F A B) (x:V) (u w:B)
    (hu:x=(P.left u).val∨x=(P.right u).val)
    (hw:x=(P.left w).val∨x=(P.right w).val):u=w:=by
  rcases hu with hu|hu <;> rcases hw with hw|hw
  · exact P.left.injective (Subtype.ext (hu.symm.trans hw))
  · exact (P.left_ne_right u w (hu.symm.trans hw)).elim
  · exact (P.left_ne_right w u (hw.symm.trans hu)).elim
  · exact P.right.injective (Subtype.ext (hu.symm.trans hw))

theorem graph_degree (P:EndpointPairing G F A B) (x:V):P.graph.degree x≤2:=by
  have hrow (u:B):((P.left u).val∉B)∧((P.right u).val∉B):=
    ⟨fun h=>Finset.disjoint_left.mp P.disjoint_parts (P.left u).property h,
      fun h=>Finset.disjoint_left.mp P.disjoint_parts (P.right u).property h⟩
  rw [←SimpleGraph.card_neighborFinset_eq_degree]
  by_cases hx:x∈B
  · let z:B:=⟨x,hx⟩
    have hs:P.graph.neighborFinset x⊆{(P.left z).val,(P.right z).val}:=by
      intro y hy
      obtain ⟨u,⟨hxu,hyu⟩|⟨hyu,hxu⟩⟩:=(P.graph.mem_neighborFinset x y).mp hy
      · have he:u=z:=Subtype.ext hxu.symm
        rw [he] at hyu
        simpa only [Finset.mem_insert,Finset.mem_singleton] using hyu
      · rcases hxu with hxu|hxu
        · exact ((hrow u).1 (hxu ▸ hx)).elim
        · exact ((hrow u).2 (hxu ▸ hx)).elim
    apply (Finset.card_le_card hs).trans
    have hh:=Finset.card_insert_le (P.left z).val ({(P.right z).val}:Finset V)
    simpa only [Finset.card_singleton] using hh
  · by_cases hz:∃ u:B,x=(P.left u).val∨x=(P.right u).val
    · obtain ⟨z,hz⟩:=hz
      have hs:P.graph.neighborFinset x⊆{z.val}:=by
        intro y hy
        obtain ⟨u,⟨hxu,hyu⟩|⟨hyu,hxu⟩⟩:=(P.graph.mem_neighborFinset x y).mp hy
        · exact (hx (hxu ▸ u.property)).elim
        · have he:u=z:=P.row_hub_unique x u z hxu hz
          rw [he] at hyu
          exact Finset.mem_singleton.mpr hyu
      have hh: (P.graph.neighborFinset x).card≤1:=by simpa only [Finset.card_singleton] using Finset.card_le_card hs
      omega
    · have hs:P.graph.neighborFinset x=∅:=by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        obtain ⟨u,⟨hxu,hyu⟩|⟨hyu,hxu⟩⟩:=(P.graph.mem_neighborFinset x y).mp hy
        · exact hx (hxu ▸ u.property)
        · exact hz ⟨u,hxu⟩
      rw [hs];simp

theorem graph_disjoint (P:EndpointPairing G F A B) (K:SimpleGraph V)
    (h:Disjoint G K):Disjoint P.graph K:=by
  apply h.mono_left
  intro x y hxy
  exact ((spanningRestriction_adj G (A∪B) x y).mp (P.graph_le hxy)).1

theorem graph_support (P:EndpointPairing G F A B):P.graph.support.toFinset=A∪B:=by
  ext x
  simp only [Set.mem_toFinset,SimpleGraph.mem_support,Finset.mem_union]
  constructor
  · rintro ⟨y,hxy⟩
    have hh:=(spanningRestriction_adj G (A∪B) x y).mp (P.graph_le hxy)
    exact Finset.mem_union.mp hh.2.1
  · rintro (hx|hx)
    · rcases P.cover ⟨x,hx⟩ with ⟨u,hu⟩|⟨u,hu⟩
      · exact ⟨u.val,u,Or.inr ⟨rfl,Or.inl (congrArg Subtype.val hu).symm⟩⟩
      · exact ⟨u.val,u,Or.inr ⟨rfl,Or.inr (congrArg Subtype.val hu).symm⟩⟩
    · let u:B:=⟨x,hx⟩
      exact ⟨(P.left u).val,u,Or.inl ⟨rfl,Or.inl rfl⟩⟩

def mono (P:EndpointPairing G F A B) (Q:SimpleGraph V) (hG:G≤Q):EndpointPairing Q F A B where
  disjoint_parts:=P.disjoint_parts
  left:=P.left
  right:=P.right
  adjacent:=fun u=>⟨hG (P.adjacent u).1,hG (P.adjacent u).2⟩
  avoid:=P.avoid
  disjoint_ranges:=P.disjoint_ranges
  cover:=P.cover

theorem mono_graph (P:EndpointPairing G F A B) (Q:SimpleGraph V) (hG:G≤Q):
    (P.mono Q hG).graph=P.graph:=rfl

theorem deleted_graph_choice (Q D F:SimpleGraph V) (A B:Finset V)
    (h:Nonempty (EndpointPairing (Q\D) F A B)):
    ∃ P:EndpointPairing Q F A B,Disjoint P.graph D:=by
  obtain ⟨P⟩:=h
  refine ⟨P.mono Q (fun _ _ h=>h.1),?_⟩
  rw [mono_graph]
  apply disjoint_iff_inf_le.mpr
  intro x y hxy
  have hg:=((spanningRestriction_adj (Q\D) (A∪B) x y).mp (P.graph_le hxy.1)).1
  exact (hg.2 hxy.2).elim

end EndpointPairing
end Oberwolfach
