module

public import Oberwolfach.MarkedVortexDensityMass

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_hub_cardinality_le_host
    {n D:ℕ} {U:Type} [Fintype U] {G:SimpleGraph (Fin n)}
    (hreg:G.IsRegularOfDegree D) (hn:0<n) (hD:0<D)
    (hρ:initialIndexDensity U D≤1):Fintype.card U≤n:=by
  have hDpos:(0:ℝ)<D:=by exact_mod_cast hD
  have hmass:2*(Fintype.card U:ℝ)≤D:=by
    have hh:=(div_le_iff₀ hDpos).1 hρ
    simpa [initialIndexDensity] using hh
  have hDn:D≤n:=by simpa only [Fintype.card_fin] using (regular_degree_le_card hreg (by simpa using hn))
  have hDnR:(D:ℝ)≤n:=by exact_mod_cast hDn
  have hu:(0:ℝ)≤Fintype.card U:=Nat.cast_nonneg _
  have hh:(Fintype.card U:ℝ)≤n:=by linarith
  exact_mod_cast hh
end Oberwolfach
