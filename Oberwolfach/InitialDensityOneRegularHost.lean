module

public import Oberwolfach.Vortex

@[expose] public section
/-! At density one the host degree equals twice the number of prescribed
factor indices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem initial_density_one_regular_host {V U:Type} [Fintype V] [Fintype U]
    (P:SimpleGraph V) (D:ℕ) (hD:0<D) (hreg:P.IsRegularOfDegree D)
    (hone:initialIndexDensity U D=1):
    P.IsRegularOfDegree (2*Fintype.card U):=by
  have hDpos:(D:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hD)
  have hMass:initialIndexDensity U D*(D:ℝ)=2*Fintype.card U:=by
    simp [initialIndexDensity,hDpos]
  have hreal:(D:ℝ)=2*Fintype.card U:=by simpa only [hone,one_mul] using hMass
  have hnat:D=2*Fintype.card U:=by exact_mod_cast hreal
  simpa only [←hnat] using hreg
end Oberwolfach
