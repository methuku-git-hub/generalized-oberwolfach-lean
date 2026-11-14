module

public import Oberwolfach.SparseCorrectionMatrices

@[expose] public section
/-! The finite-cut property does not depend on which finite and decidable
instances present the same underlying finite types. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem bipartite_large_cut_reinstance {X Y:Type} {fx fx':Fintype X} {fy fy':Fintype Y}
    {dx dx':DecidableEq X} {dy dy':DecidableEq Y} {L:X→Y→ℕ} {δ h:ℝ}
    (hc:@BipartiteLargeCut X Y fx fy dx dy L δ h):
    @BipartiteLargeCut X Y fx' fy' dx' dy' L δ h:=by
  have hfx:fx=fx':=Subsingleton.elim _ _
  have hfy:fy=fy':=Subsingleton.elim _ _
  have hdx:dx=dx':=Subsingleton.elim _ _
  have hdy:dy=dy':=Subsingleton.elim _ _
  cases hfx
  cases hfy
  cases hdx
  cases hdy
  exact hc
end Oberwolfach
