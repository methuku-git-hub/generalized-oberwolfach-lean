module

public import Oberwolfach.OrdinaryExpansionDegrees

@[expose] public section

/-! Degree balance and hub divisibility under disjoint unions of actual
rim graphs and spoke relations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem graph_degree_disjoint_sup (G K : SimpleGraph V) (h : Disjoint G K) (a : V) :
    (G⊔K).degree a=G.degree a+K.degree a := by
  have hd : Disjoint (G.neighborFinset a) (K.neighborFinset a) := by
    apply Finset.disjoint_left.mpr
    intro b hb hk
    have hG := (SimpleGraph.mem_neighborFinset (G:=G) (v:=a) b).mp hb
    have hK := (SimpleGraph.mem_neighborFinset (G:=K) (v:=a) b).mp hk
    exact disjoint_iff_inf_le.mp h ⟨hG,hK⟩
  rw [←SimpleGraph.card_neighborFinset_eq_degree,SimpleGraph.neighborFinset_sup,
    Finset.card_union_of_disjoint hd,SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.card_neighborFinset_eq_degree]

theorem card_filter_disjoint_or {A : Type*} [Fintype A] [DecidableEq A]
    (p q : A → Prop) [DecidablePred p] [DecidablePred q] (h : ∀ a,¬(p a ∧ q a)) :
    (Finset.univ.filter (fun a => p a ∨ q a)).card=
      (Finset.univ.filter p).card+(Finset.univ.filter q).card := by
  have he : Finset.univ.filter (fun a => p a ∨ q a)=(Finset.univ.filter p)∪(Finset.univ.filter q) := by ext;simp
  rw [he,Finset.card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro a hp hq
  exact h a ⟨(Finset.mem_filter.mp hp).2,(Finset.mem_filter.mp hq).2⟩

theorem ordinary_balance_disjoint_union (G K : SimpleGraph V) (H J : V → U → Prop)
    (hGK : Disjoint G K) (hHJ : ∀ a b,¬(H a b ∧ J a b))
    (hG : ∀ a,G.degree a=2*(Finset.univ.filter (H a)).card)
    (hK : ∀ a,K.degree a=2*(Finset.univ.filter (J a)).card) :
    ∀ a,(G⊔K).degree a=2*(Finset.univ.filter (fun b => H a b ∨ J a b)).card := by
  intro a
  rw [graph_degree_disjoint_sup G K hGK,card_filter_disjoint_or (H a) (J a) (hHJ a),hG,hK]
  omega

theorem ordinary_hub_divisibility_disjoint_union (H J : V → U → Prop) (r : ℕ)
    (hHJ : ∀ a b,¬(H a b ∧ J a b))
    (hH : ∀ b,r ∣ (Finset.univ.filter (fun a => H a b)).card)
    (hJ : ∀ b,r ∣ (Finset.univ.filter (fun a => J a b)).card) :
    ∀ b,r ∣ (Finset.univ.filter (fun a => H a b ∨ J a b)).card := by
  intro b
  rw [card_filter_disjoint_or (fun a => H a b) (fun a => J a b) (fun a => hHJ a b)]
  exact dvd_add (hH b) (hJ b)

end Oberwolfach
