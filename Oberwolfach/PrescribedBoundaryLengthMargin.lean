module

public import Oberwolfach.PrescribedBoundaryMatchingLoadBudget

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem prescribed_boundary_length_margin
    (d:ℕ) (θ δ:ℝ) (hθ:0≤θ) (hinv:1/(d:ℝ)≤θ/1024) (hθδ:10*θ≤δ):
    4/(d:ℝ)≤δ/8:=by
  have he:4/(d:ℝ)=4*(1/(d:ℝ)):=by ring
  rw [he]
  linarith only [hθ,hinv,hθδ]
end Oberwolfach
