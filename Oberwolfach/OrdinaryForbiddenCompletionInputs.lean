module

public import Oberwolfach.OrdinaryRequiredAvoidsForbidden

@[expose] public section
/-! The same residual placement that covers the enlarged required graph gives
both the protected-pair input and forbidden-edge-free actual remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reference_minus_forbidden_disjoint {V:Type} [Fintype V] [DecidableEq V]
    (Reference Bad:SimpleGraph V):Disjoint (Reference\Bad) Bad:=by
  apply disjoint_iff_inf_le.mpr
  intro v w h
  exact h.1.2 h.2

theorem ordinary_forbidden_placement_completion_inputs {n q:ℕ}
    (Target Sample Reference Bad:SimpleGraph (Fin n)) (Inner:Finset (Fin n))
    (Fs:Fin q→SimpleGraph (Fin n))
    (C:∀u,Finset (Fs u).ConnectedComponent)
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (Old New:Fin q→Finset (Sym2 (Fin n)))
    (hpartition:∀u,(((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).edgeFinset).image
      (Sym2.map (f u))=Old u∪New u)
    (hcover:∀e∈(ordinaryForbiddenRequired Target Sample Reference Bad Inner).edgeFinset,∃u,e∈New u):
    ordinaryProtectedRequired Target Sample Reference Inner≤ordinaryEmbeddedComplements Fs C f ∧
    Disjoint (Target\ordinaryEmbeddedComplements Fs C f) Bad ∧
    (∀v w,(Target\ordinaryEmbeddedComplements Fs C f).Adj v w→¬Bad.Adj v w):=by
  have hG:ordinaryForbiddenRequired Target Sample Reference Bad Inner≤ordinaryEmbeddedComplements Fs C f:=
    ordinary_required_edges_covered_by_complements _ Fs C f Old New hpartition hcover
  have hP:ordinaryProtectedRequired Target Sample Reference Inner≤ordinaryEmbeddedComplements Fs C f:=
    le_trans le_sup_left hG
  have hB:Target⊓Bad≤ordinaryEmbeddedComplements Fs C f:=le_trans le_sup_right hG
  have hd:=ordinary_forbidden_remainder_free Target Bad (ordinaryEmbeddedComplements Fs C f) hB
  refine ⟨hP,hd,?_⟩
  intro v w hr hb
  exact (disjoint_iff_inf_le.mp hd) ⟨hr,hb⟩
end Oberwolfach
