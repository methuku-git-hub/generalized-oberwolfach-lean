module

public import Oberwolfach.ResidualOrdinaryMassFromSource

@[expose] public section
/-! Transfer the upper half of the source count estimate to actual cycles. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem residual_ordinary_mass_upper_from_source_count
    {V K J:Type} [Fintype V] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph V} (a:ActualResidualData (K:=K) (J:=J) F)
    (hEmbed:a.Cembed=a.t.biUnion (fun j=>(a.C j).support.toFinset))
    (sourceMass:ℕ) (hcard:a.Cembed.card=sourceMass) (target err:ℝ)
    (hsource:|((sourceMass:ℝ)-target)|≤err):
    ((a.t.biUnion (fun j=>(a.C j).support.toFinset)).card:ℝ)≤target+err:=by
  have h:= (abs_le.mp hsource).2
  rw [hEmbed] at hcard
  rw [←hcard] at h
  linarith
end Oberwolfach
