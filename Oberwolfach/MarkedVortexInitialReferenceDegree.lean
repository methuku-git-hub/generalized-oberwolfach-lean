module

public import Oberwolfach.MarkedVortexInitialExtendedEquivs

@[expose] public section
/-! The level-zero reference degree is the original regular host degree. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    {P:SimpleGraph (Fin n)} {D m:ℕ} {β ε:ℝ}

theorem marked_vortex_initial_reference_degree
    (Q:Vortex U P D β ε m) (ρ:ℝ) (hρ:0<ρ) (hsize:ρ*D=2*Fintype.card U):
    2*(Fintype.card (markedVortexHubType Q 0):ℝ)/ρ=D:=by
  have hcard:Fintype.card (markedVortexHubType Q 0)=Fintype.card U:=
    Fintype.card_congr (markedVortexInitialExtendedHubEquiv Q)
  rw [hcard]
  have hρne:ρ≠0:=ne_of_gt hρ
  field_simp
  nlinarith [hsize]
end Oberwolfach
