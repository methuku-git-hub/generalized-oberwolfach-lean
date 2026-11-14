module

public import Oberwolfach.PrescribedBoundaryMarginsAsymptotic

@[expose] public section
/-! The boundary contribution can be made small by choosing the spacing and
then the order; no wheel-length lower bound is used in this estimate. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_boundary_load_spacing_and_order
    (δ:ℝ) (hδ:0<δ):
    ∃d₀ N:ℕ,2≤d₀ ∧ 1≤N ∧ ∀d≥d₀,∀n≥N,
      4/(d:ℝ)≤δ/16 ∧ 4*(n:ℝ)^(3/4:ℝ)≤δ*n/16 :=by
  obtain ⟨d₀,N,hd₀,hN,hMargins⟩:=prescribed_boundary_margins_eventually (δ/2) (by linarith)
  refine ⟨max d₀ 2,N,le_max_right _ _,hN,?_⟩
  intro d hd n hn
  obtain ⟨h1,h2⟩:=hMargins d (by omega) n hn
  constructor <;> linarith
end Oberwolfach
