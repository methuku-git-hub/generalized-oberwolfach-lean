module

public import Oberwolfach.LongClassRequiredNonInnerDegree

@[expose] public section
/-! If a physical edit is supported on required edges and leaves the
protected inner graph unchanged, its degree depends only on the spacing. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V]

theorem long_class_required_change_outside_inner
    (P S Sel Used G H:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V)
    (Req:V→V→Prop) (Pack:Finset (Sym2 V)) (hSP:S≤P):
    let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
    let Kplus:=longClassInnerRequiredRepair S Used K I Pack
    let Change:=(G\H)⊔(H\G);
    Change≤Kplus→(∀v∈I,∀w∈I,G.Adj v w↔H.Adj v w)→
      ∀v,Change.degree v≤6*d+2 :=by
  intro K Kplus Change hsub hagree v
  let Koutside:=Kplus\spanningRestriction (⊤:SimpleGraph V) I
  have hEdges:Change≤Koutside:=by
    intro x y hxy
    have hk:Kplus.Adj x y:=hsub hxy
    change Kplus.Adj x y ∧ ¬(spanningRestriction (⊤:SimpleGraph V) I).Adj x y
    refine ⟨hk,?_⟩
    intro hi
    have hi':= (spanningRestriction_adj _ _ _ _).mp hi
    have heq:=hagree x hi'.2.1 y hi'.2.2
    change (G.Adj x y ∧ ¬H.Adj x y) ∨ (H.Adj x y ∧ ¬G.Adj x y) at hxy
    rcases hxy with h|h
    · exact h.2 (heq.mp h.1)
    · exact h.2 (heq.mpr h.1)
  have hs:Change.neighborFinset v⊆Koutside.neighborFinset v:=by
    intro w hw
    exact (SimpleGraph.mem_neighborFinset _ _ _).mpr (hEdges ((SimpleGraph.mem_neighborFinset _ _ _).mp hw))
  have hc:=Finset.card_le_card hs
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hc
  exact hc.trans (long_class_required_non_inner_degree P S Sel Used π d I Req Pack hSP v)
end Oberwolfach
