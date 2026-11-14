module

public import Oberwolfach.ExpandedClassDensityIdentity

@[expose] public section
/-! The actual long-selector probabilities have total physical mass one
when the index class has density one. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem long_selector_density_one_mass {U:Type} [Fintype U]
    (ρ D s:ℝ) (a b:U→ℝ) (hD:D≠0) (hsize:ρ*D=2*Fintype.card U) (hone:ρ=1):
    2*(ρ*(1/100)/2)+2*(ρ*s/2)+2*((∑u,b u)/D)+2*((∑u,a u)/D)+
      2*(∑u,(1-1/100-s-a u-b u))/D=1 :=by
  have h:=expanded_class_density_identity ρ D (1/100) s a b hD hsize
  rw [hone] at h ⊢
  convert h using 1 <;> ring
end Oberwolfach
