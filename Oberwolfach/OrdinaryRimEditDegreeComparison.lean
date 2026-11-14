module

public import Oberwolfach.OrdinaryRemainderReferenceEdits

@[expose] public section
/-! A symmetric rim-edit bound controls the increase of every degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem ordinary_rim_degree_le_reference_add_edits
    (Q Reference:SimpleGraph V) (b:ℝ)
    (hEdit:∀v,((Finset.univ.filter (fun w=>Xor (Q.Adj v w) (Reference.Adj v w))).card:ℝ)≤b):
    ∀v,(Q.degree v:ℝ)≤(Reference.degree v:ℝ)+b:=by
  intro v
  let C:=Finset.univ.filter (fun w=>Xor (Q.Adj v w) (Reference.Adj v w))
  have hsub:Q.neighborFinset v⊆Reference.neighborFinset v∪C:=by
    intro w hw
    have hq:Q.Adj v w:=(Q.mem_neighborFinset v w).mp hw
    by_cases hr:Reference.Adj v w
    · exact Finset.mem_union_left _ ((Reference.mem_neighborFinset v w).mpr hr)
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl ⟨hq,hr⟩⟩
  have hc: (Q.neighborFinset v).card≤(Reference.neighborFinset v).card+C.card:=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hc':(Q.degree v:ℝ)≤(Reference.degree v:ℝ)+C.card:=by
    have hcast:((Q.neighborFinset v).card:ℝ)≤(Reference.neighborFinset v).card+C.card:=by exact_mod_cast hc
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hcast
  have he:(C.card:ℝ)≤b:=hEdit v
  linarith
end Oberwolfach
