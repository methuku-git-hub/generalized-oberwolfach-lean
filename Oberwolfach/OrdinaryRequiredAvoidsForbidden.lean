module

public import Oberwolfach.OrdinaryProtectedRequiredEdges
public import Oberwolfach.OrdinaryRequiredEdgesCovered

@[expose] public section
/-! Include all target edges of the bounded forbidden graph among the
required edges. The earlier matching deletes that graph, while the protected
reference remains untouched; the remainder is then forbidden-edge-free. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

def ordinaryForbiddenRequired (Target Sample Reference Bad:SimpleGraph V) (Inner:Finset V):SimpleGraph V:=
  ordinaryProtectedRequired Target Sample Reference Inner⊔(Target⊓Bad)

def ordinaryForbiddenSampleDeletion (Sample Target Reference Protect Bad:SimpleGraph V) (Inner:Finset V):SimpleGraph V:=
  ordinaryProtectedSampleDeletion Sample Target Reference Protect Inner⊔Bad

theorem ordinary_forbidden_required_relations
    (Target Sample Reference Protect Bad:SimpleGraph V) (Inner:Finset V)
    (hRef:Reference≤Sample) (hProtect:Protect≤Reference) (hBad:Disjoint Reference Bad):
    let G:=ordinaryForbiddenRequired Target Sample Reference Bad Inner
    let Del:=ordinaryForbiddenSampleDeletion Sample Target Reference Protect Bad Inner;
    G≤Target\Protect ∧ Sample\Del≤Target\Protect ∧
    (∀v w,G.Adj v w→¬(Sample\Del).Adj v w) ∧
    Target⊓Bad≤G ∧ ordinaryProtectedRequired Target Sample Reference Inner≤G:=by
  intro G Del
  have h:=ordinary_protected_required_edges_relations Target Sample Reference Protect Inner hRef hProtect
  constructor
  · intro v w he
    rcases he with he|he
    · exact h.1 he
    · refine ⟨he.1,?_⟩
      intro hp
      exact (disjoint_iff_inf_le.mp hBad) ⟨hProtect hp,he.2⟩
  constructor
  · intro v w he
    apply h.2.1
    exact ⟨he.1,fun hdel=>he.2 (Or.inl hdel)⟩
  constructor
  · intro v w hg hs
    rcases hg with hg|hg
    · apply h.2.2.2 v w hg
      exact ⟨hs.1,fun hd=>hs.2 (Or.inl hd)⟩
    · exact hs.2 (Or.inr hg.2)
  exact ⟨le_sup_right,le_sup_left⟩

theorem ordinary_forbidden_remainder_free
    (Target Bad Embedded:SimpleGraph V) (hcover:Target⊓Bad≤Embedded):
    Disjoint (Target\Embedded) Bad:=by
  apply disjoint_iff_inf_le.mpr
  intro v w hh
  exact hh.1.2 (hcover ⟨hh.1.1,hh.2⟩)

theorem ordinary_forbidden_required_degree_bounds
    (Target Sample Reference Protect Bad:SimpleGraph V) (Inner:Finset V) (x:V):
    (ordinaryForbiddenRequired Target Sample Reference Bad Inner).degree x≤
      (ordinaryProtectedRequired Target Sample Reference Inner).degree x+Bad.degree x ∧
    (ordinaryForbiddenSampleDeletion Sample Target Reference Protect Bad Inner).degree x≤
      (ordinaryProtectedSampleDeletion Sample Target Reference Protect Inner).degree x+Bad.degree x:=by
  constructor
  · have hh:=graph_degree_sup_le (ordinaryProtectedRequired Target Sample Reference Inner) (Target⊓Bad) x
    have hh':(ordinaryForbiddenRequired Target Sample Reference Bad Inner).degree x≤
        (ordinaryProtectedRequired Target Sample Reference Inner).degree x+(Target⊓Bad).degree x:=by
      convert hh using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
    have hi:(Target⊓Bad).degree x≤Bad.degree x:=SimpleGraph.degree_le_of_le inf_le_right
    omega
  · have hh:=graph_degree_sup_le (ordinaryProtectedSampleDeletion Sample Target Reference Protect Inner) Bad x
    convert hh using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
end Oberwolfach
