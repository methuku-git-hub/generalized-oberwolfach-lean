module

public import Oberwolfach.ColourRoundErrorMargins

@[expose] public section
/-! An eventual local correction budget follows from a strict linear gap. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_local_correction_eventually
    (d:ℕ) (eta Δ b a γ αAssign κ:ℝ)
    (hrate:Δ+2*(b+2*max a γ+αAssign/16+κ)<eta):
    ∃N:ℕ,∀n:ℕ,N≤n→
      (n:ℝ)^(3/5:ℝ)+(d:ℝ)*(n:ℝ)^(3/5:ℝ)+
        (Δ*n+2*((b*n+2*(max a γ*n))+(αAssign/16)*n+(κ*n+1))+(6*d+2:ℕ))≤eta*n :=by
  let L:ℝ:=Δ+2*(b+2*max a γ+αAssign/16+κ)
  let C:ℝ:=2+(6*d+2:ℕ)
  let gap:=eta-L
  have hgap:0<gap:=by dsimp [gap,L];linarith
  have hC:0≤C:=by dsimp [C];positivity
  obtain ⟨N,hN⟩:=eventually_sublinear_affine_error (1+d) C 1 (2/5) gap
    (by positivity) hC (by norm_num) (by norm_num) hgap
  refine ⟨N,?_⟩
  intro n hn
  have herr:=hN n hn ((n:ℝ)^(3/5:ℝ)) (by norm_num)
  have heq:(n:ℝ)^(3/5:ℝ)+(d:ℝ)*(n:ℝ)^(3/5:ℝ)+
      (Δ*n+2*((b*n+2*(max a γ*n))+(αAssign/16)*n+(κ*n+1))+(6*d+2:ℕ))=
      L*n+(1+d)*(n:ℝ)^(3/5:ℝ)+C:=by dsimp [L,C];push_cast;ring
  rw [heq]
  dsimp [gap] at herr
  nlinarith
end Oberwolfach
