module

public import Oberwolfach.MarkedResourceRimGraph

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_resource_rim_graph_edge_card_le
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (C:Finset (Finset V ⊕ (V×U))):
    (markedResourceRimGraph C).edgeFinset.card≤C.card := by
  have hmem:∀e:Sym2 V,e∈(markedResourceRimGraph C).edgeFinset→Sum.inl e.toFinset∈C:=by
    intro e
    induction e using Sym2.ind with
    | _ x y =>
      intro he
      have ha:(markedResourceRimGraph C).Adj x y:=by simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using he
      change x≠y ∧ ({x,y}:Finset V)∈markedResourceRimEdges C at ha
      simpa only [Sym2.toFinset_mk_eq] using (Finset.mem_filter.mp ha.2).2
  let f:{e // e∈(markedResourceRimGraph C).edgeFinset}→{e // e∈C}:=
    fun e=>⟨Sum.inl e.val.toFinset,hmem e.val e.property⟩
  have hf:Function.Injective f:=by
    intro a b h
    apply Subtype.ext
    apply Sym2.ext
    intro x
    have he:a.val.toFinset=b.val.toFinset:=Sum.inl.inj (congrArg Subtype.val h)
    simpa only [←Sym2.mem_toFinset,he]
  have hcard:=Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe] using hcard
end Oberwolfach
