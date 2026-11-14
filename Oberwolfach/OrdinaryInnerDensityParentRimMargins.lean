module

public import Oberwolfach.OrdinaryEndpointDegreeFromInnerDensity
public import Oberwolfach.OrdinaryInducedRimThresholdHalfDensity

@[expose] public section
/-! The single inner-density margin used for parent triangle weights also
    supplies the endpoint and induced rim minimum-degree inputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_inner_density_parent_rim_margins
    {V:Type} [Fintype V] [DecidableEq V] (P:SimpleGraph V) (A:Finset V) (density α:ℝ)
    (hα:0≤α) (hthreshold:cycleThreshold 3+α≤density)
    (hmin:∀v,density*A.card≤((A∩P.neighborFinset v).card:ℝ)) :
    cycleThreshold 3≤density ∧ (1/2:ℝ)+α≤density ∧
    (∀x∉A,∀v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ)) ∧
    (∀v:A,(1/2+α)*A.card≤((P.induce (A:Set V)).degree v:ℝ)) := by
  have hθ : cycleThreshold 3≤density := by linarith
  have hhalf : (1/2:ℝ)+α≤density := by
    have hh:=cycleThreshold_half_le (by omega : 3≤3)
    linarith
  exact ⟨hθ,hhalf,ordinary_endpoint_degree_from_inner_density P A density hθ hmin,
    ordinary_induced_rim_threshold_from_half_density P A density α hhalf (fun v _=>hmin v)⟩
end Oberwolfach
