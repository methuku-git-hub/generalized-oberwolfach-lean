module

public import Oberwolfach.FirstVortexNoMarkedLateClassesScales

@[expose] public section
/-! Fold the remaining explicit size bounds into the same asymptotic list threshold. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_list_threshold_with_size
    (d:ℕ) (γList pstar βlist lamList ζList βfinal δglobal:ℝ)
    (N:ℕ)
    (hList:∀n≥N,
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γList*pstar^2*n ∧
      βlist*n+(n:ℝ)^(3/4:ℝ)≤γList*pstar^2*n*(1/100:ℝ) ∧
      (lamList+2*ζList)*n≤βlist*n):
    ∃Ntotal:ℕ,∀n≥Ntotal,
      2≤n ∧ 100/βfinal≤(n:ℝ) ∧ 2/Real.sqrt δglobal≤(n:ℝ) ∧
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γList*pstar^2*n ∧
      βlist*n+(n:ℝ)^(3/4:ℝ)≤γList*pstar^2*n*(1/100:ℝ) ∧
      (lamList+2*ζList)*n≤βlist*n:=by
  obtain ⟨Nβ,hNβ⟩:=exists_nat_gt (100/βfinal)
  obtain ⟨Nδ,hNδ⟩:=exists_nat_gt (2/Real.sqrt δglobal)
  refine ⟨max (max N 2) (max Nβ Nδ),?_⟩
  intro n hn
  have hnN:N≤n:=by omega
  have hn2:2≤n:=by omega
  have hnβ:(Nβ:ℝ)≤n:=by exact_mod_cast (show Nβ≤n by omega)
  have hnδ:(Nδ:ℝ)≤n:=by exact_mod_cast (show Nδ≤n by omega)
  exact ⟨hn2,le_trans (le_of_lt hNβ) hnβ,le_trans (le_of_lt hNδ) hnδ,hList n hnN⟩
end Oberwolfach
