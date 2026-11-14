module

public import Oberwolfach.HypergraphColourCliques
public import Oberwolfach.ListColouringLocalLemma

@[expose] public section

/-! Restriction of indexed hyperedges preserves every resource degree and
codegree. A final large list-to-degree ratio supplies a proper colouring. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem subtype_filter_card_le {E : Type*} [Fintype E]
    (P Q : E → Prop) :
    (Finset.univ.filter (fun e : {e // P e} => Q e.val)).card≤
      (Finset.univ.filter Q).card := by
  classical
  apply Finset.card_le_card_of_injOn (f := Subtype.val)
  · intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp he).2⟩
  · intro e _ f _ hef
    exact Subtype.ext hef

theorem hypergraph_subtype_resource_degree {V E : Type*} [Fintype E]
    (R : E → Finset V) (P : E → Prop) (v : V) :
    (hypergraphVertexClique (fun e : {e // P e}=>R e.val) v).card≤
      (hypergraphVertexClique R v).card := by
  convert subtype_filter_card_le P (fun e=>v∈R e) using 1 <;>
    congr 1 <;> ext e <;> simp only [hypergraphVertexClique,Finset.mem_filter]

theorem hypergraph_subtype_codegree {V E : Type*} [Fintype E]
    (R : E → Finset V) (P : E → Prop) (u v : V) :
    (Finset.univ.filter (fun e : {e // P e}=>u∈R e.val ∧ v∈R e.val)).card≤
      (Finset.univ.filter (fun e=>u∈R e ∧ v∈R e)).card :=
  by
    convert subtype_filter_card_le P (fun e=>u∈R e ∧ v∈R e) using 1 <;>
      congr 1 <;> ext e <;> simp only [Finset.mem_filter]

theorem hypergraph_subtype_adj {V E : Type*} (R : E → Finset V) (P : E → Prop)
    (e f : {e // P e}) :
    (hypergraphLineGraph (fun e : {e // P e}=>R e.val)).Adj e f ↔
      (hypergraphLineGraph R).Adj e.val f.val := by
  constructor
  · rintro ⟨hne,hdis⟩
    exact ⟨fun h=>hne (Subtype.ext h),hdis⟩
  · rintro ⟨hne,hdis⟩
    exact ⟨fun h=>hne (congrArg Subtype.val h),hdis⟩

theorem hypergraph_list_colouring_at_large_ratio
    {V E C : Type*} [Fintype E] [Fintype C]
    (R : E → Finset V) (L : E → Finset C) {k l s : ℕ}
    (hk : 0<k) (hs : 0<s) (hsize : ∀ e,(R e).card≤k)
    (hcard : ∀ e,(L e).card=l)
    (hdegree : ∀ v c,(hypergraphColourClique R L v c).card≤s)
    (hlarge : 16*(k*s)≤l) :
    ∃ f : E → C,(∀ e,f e∈L e) ∧ ∀ e g,(hypergraphLineGraph R).Adj e g → f e≠f g := by
  apply finite_list_colouring_of_colour_degree (hypergraphLineGraph R) L
    (mul_pos hk hs) hcard ?_ hlarge
  intro e c
  exact hypergraph_colour_neighbour_degree R L hsize c (fun v=>hdegree v c) e

end Oberwolfach
