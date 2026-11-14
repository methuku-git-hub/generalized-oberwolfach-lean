module

public import Oberwolfach.ExpandedClassDensityIdentity
public import Oberwolfach.ExpandedClassMass

@[expose] public section
/-! The long-class sampling recipe has exactly the original class density,
and its selected probability is uniformly bounded by the original density
lower bound. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem long_expanded_class_density_and_floor
    {U:Type} [Fintype U] (ρ₀ ρ D s:ℝ) (a b:U→ℝ)
    (hD:0<D) (hρ:ρ₀≤ρ) (hsize:ρ*D=2*Fintype.card U):
    ρ₀/200≤ρ*(1/100)/2 ∧
    (∑j∈({0,1,2,3,4}:Finset (Fin 6)),
      markedExpandedPhysicalProbability (ρ*(1/100)/2) (ρ*s/2)
        ((∑u,b u)/D) ((∑u,a u)/D) (2*(∑u,(1-1/100-s-a u-b u))/D) j)=ρ:=by
  constructor
  · linarith
  · rw [expanded_physical_class_mass]
    have hh:=expanded_class_density_identity ρ D (1/100) s a b (ne_of_gt hD) hsize
    convert hh using 1 <;> ring
end Oberwolfach
