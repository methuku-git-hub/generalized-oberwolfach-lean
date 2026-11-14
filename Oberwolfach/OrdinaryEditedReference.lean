module

public import Oberwolfach.OrdinaryProtectedInnerRim

@[expose] public section
/-! The reference obtained by removing edges lost in the edit is contained
    in both the original sample and the edited target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

def ordinaryEditedReference (Reference Sample Target:SimpleGraph V):SimpleGraph V :=
  Reference\(Sample\Target)

theorem ordinary_edited_reference_containment
    (Reference Sample Target:SimpleGraph V) (hRef:Reference≤Sample):
    ordinaryEditedReference Reference Sample Target≤Reference ∧
    ordinaryEditedReference Reference Sample Target≤Sample ∧
    ordinaryEditedReference Reference Sample Target≤Target:=by
  refine ⟨sdiff_le,(sdiff_le.trans hRef),?_⟩
  intro v w he
  by_contra ht
  exact he.2 ⟨hRef he.1,ht⟩

theorem ordinary_edited_reference_lost_degree
    (Reference Sample Target:SimpleGraph V) (hRef:Reference≤Sample) (b:ℝ)
    (hEdit:∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤b):
    ∀v,((Reference\ordinaryEditedReference Reference Sample Target).degree v:ℝ)≤b:=by
  intro v
  have hsub:Reference\ordinaryEditedReference Reference Sample Target≤Sample\Target:=by
    intro x y he
    have hs:Sample.Adj x y:=hRef he.1
    by_contra hnot
    exact he.2 ⟨he.1,hnot⟩
  have hh:=SimpleGraph.degree_le_of_le hsub (v:=v)
  have hl:=lost_graph_degree_le_symmetric_edit Target Sample b hEdit v
  have hh':((Reference\ordinaryEditedReference Reference Sample Target).degree v:ℝ)≤
      ((Sample\Target).degree v:ℝ):=by exact_mod_cast hh
  exact hh'.trans hl
end Oberwolfach
