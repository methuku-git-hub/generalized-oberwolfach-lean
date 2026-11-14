module

public import Oberwolfach.PositiveClassComplement
public import Oberwolfach.Vortex

@[expose] public section
/-! The vortex index density of a selected retained class inherits the
one-class versus positive-complement dichotomy. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem selected_class_index_density_dichotomy
    {I U:Type} [Fintype I] [DecidableEq I] [Fintype U] (ρ:I→ℝ) (r:ℝ) (a:I) (D:ℕ)
    (hD:0<D) (hnonneg:∀i,0≤ρ i) (htotal:∑i,ρ i=1) (hlow:∀i,r≤ρ i)
    (hsize:ρ a/2*D=Fintype.card U):
    initialIndexDensity U D=1 ∨ ∀i:Fin 2,r≤(![initialIndexDensity U D,1-initialIndexDensity U D]:Fin 2→ℝ) i:=by
  have hD':(D:ℝ)≠0:=by exact_mod_cast (ne_of_gt hD)
  have heq:initialIndexDensity U D=ρ a:=by
    unfold initialIndexDensity
    rw [←hsize]
    field_simp
  rw [heq]
  exact positive_class_binary_group_dichotomy ρ r hnonneg htotal hlow a
end Oberwolfach
