module

public import Oberwolfach.OrdinaryBoundaryCompletionAvailable

@[expose] public section
/-! A linear endpoint capacity can absorb the root-set loss as well as
the three cleanup-degree losses. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach

theorem ordinary_root_first_completion_capacity (m:ℕ) (p βe:ℝ) (hp:0<p) (hβe:0<βe):
    ∃k:ℝ,0<k ∧ ∀δ φ ρ νscale:ℝ,
      0≤δ→0≤φ→δ≤k^2→φ≤k^2→ρ≤k^2→νscale≤k^2→∃N:ℕ,
    ∀n:ℕ,N≤n→∀(Dmax:ℕ) (Lconf ν root:ℝ),
      (Dmax:ℝ)≤δ*n → Lconf≤φ*n → ν≤νscale*n → root≤(p^3*βe/4)*n →
    ∃Kcap:ℕ,0<Kcap ∧
      ((n*Dmax*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
      (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*(ρ*n)+2*((Kcap+Dmax:ℕ):ℝ))+
      (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax < (p^3*βe/2)*n-3*ν-root:=by
  have hb:0<p^3*βe/4:=by positivity
  obtain ⟨k,hk,havailable⟩:=ordinary_boundary_completion_available m (p^3*βe/4) hb
  refine ⟨k,hk,?_⟩
  intro δ φ ρ νscale hδ hφ hδk hφk hρk hνk
  obtain ⟨N,hN⟩:=havailable δ φ ρ νscale hδ hφ hδk hφk hρk hνk
  refine ⟨N,?_⟩
  intro n hn Dmax Lconf ν root hD hL hν hroot
  obtain ⟨K,hK,hbudget⟩:=hN n hn Dmax Lconf ν hD hL hν
  refine ⟨K,hK,?_⟩
  linarith only [hbudget,hroot]
end Oberwolfach
