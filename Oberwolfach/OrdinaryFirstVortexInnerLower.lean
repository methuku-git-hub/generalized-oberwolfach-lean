module

public import Oberwolfach.VortexSizeBounds

@[expose] public section
/-! The first vortex level is large enough to absorb scaled global edits. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_first_vortex_inner_lower
    {n q D mv:ℕ} {β ε:ℝ} (P:SimpleGraph (Fin n))
    (Q:Vortex (Fin q) P D β ε mv) (hε:0<ε) (hmv:0<mv):
    ε*(n:ℝ)/2≤(Q.extendedVertices 1).card :=by
  have hfirst:1≤Q.length:=by have h:=Q.length_pos; omega
  have hh:=(Q.consecutive_size_bounds hε hmv (i:=0) Q.length_pos).1
  rw [Q.initial,Finset.card_univ,Fintype.card_fin] at hh
  rw [Q.extendedVertices_eq hfirst]
  simpa using hh
end Oberwolfach
