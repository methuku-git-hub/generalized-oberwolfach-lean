module

public import Oberwolfach.OrdinaryForbiddenCompletionInputs

@[expose] public section
/-! The required edges include every edge added to the sampled host, so the
actual remainder lies inside that host even for an edited target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_forbidden_complement_le_sample {n q:ℕ}
    (Target Sample Reference Bad:SimpleGraph (Fin n)) (Inner:Finset (Fin n))
    (Fs:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (Fs u).ConnectedComponent)
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (Old New:Fin q→Finset (Sym2 (Fin n)))
    (hpartition:∀u,(((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).edgeFinset).image
      (Sym2.map (f u))=Old u∪New u)
    (hcover:∀e∈(ordinaryForbiddenRequired Target Sample Reference Bad Inner).edgeFinset,∃u,e∈New u):
    Target\ordinaryEmbeddedComplements Fs C f≤Sample :=by
  have hprotected:ordinaryProtectedRequired Target Sample Reference Inner≤ordinaryEmbeddedComplements Fs C f:=
    (ordinary_forbidden_placement_completion_inputs Target Sample Reference Bad Inner Fs C f Old New hpartition hcover).1
  have hadd:Target\Sample≤ordinaryEmbeddedComplements Fs C f:=le_trans le_sup_left hprotected
  intro v w h
  by_contra hn
  exact h.2 (hadd ⟨h.1,hn⟩)
end Oberwolfach
