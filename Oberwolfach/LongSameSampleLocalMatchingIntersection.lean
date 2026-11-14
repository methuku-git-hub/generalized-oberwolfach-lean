module

public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_same_sample_local_matching_intersection
    {Ω:Type} [Fintype Ω] (μ:FiniteLaw Ω)
    (ParentAndCorrection UniformMatching EveryClass FirstLevelTests:Ω→Prop) (a b:ℝ)
    (hMain:1-a≤μ.probability (fun z=>(ParentAndCorrection z ∧ UniformMatching z) ∧ EveryClass z))
    (hTests:1-b≤μ.probability FirstLevelTests):
    1-a-b≤μ.probability (fun z=>((ParentAndCorrection z ∧ FirstLevelTests z) ∧ UniformMatching z) ∧ EveryClass z) := by
  have hh:=finiteLaw_intersection_lower μ (fun z=>(ParentAndCorrection z ∧ UniformMatching z) ∧ EveryClass z) FirstLevelTests a b hMain hTests
  apply le_trans hh
  apply finiteLaw_probability_mono
  intro z hz
  exact ⟨⟨⟨hz.1.1.1,hz.2⟩,hz.1.1.2⟩,hz.1.2⟩
end Oberwolfach
