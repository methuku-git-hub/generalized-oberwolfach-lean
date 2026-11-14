module

public import Oberwolfach.LongResidualCycleSourceMass

@[expose] public section
/-! Transfer the already checked ordinary-source mass estimate to the cycles
in the actual residual datum. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem residual_ordinary_mass_from_source_count
    {V K J:Type} [Fintype V] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph V} (a:ActualResidualData (K:=K) (J:=J) F)
    (hEmbed:a.Cembed=a.t.biUnion (fun j=>(a.C j).support.toFinset))
    (sourceMass:ℕ) (hcard:a.Cembed.card=sourceMass) (target err:ℝ)
    (hsource:|((sourceMass:ℝ)-target)|≤err):
    target-err≤((a.t.biUnion (fun j=>(a.C j).support.toFinset)).card:ℝ):=by
  have h:= (abs_le.mp hsource).1
  rw [hEmbed] at hcard
  rw [←hcard] at h
  linarith
end Oberwolfach
