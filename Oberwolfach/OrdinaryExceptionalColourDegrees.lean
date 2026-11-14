module

public import Oberwolfach.LongPhysicalStateDegree
public import Oberwolfach.MarkedExpandedPhysicalLaw

@[expose] public section
/-! The three physical colours outside the reference and ordinary
approximate layer have small degree whenever their sampled colour degrees
are concentrated. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_exceptional_colour_degree_bounds
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (p k p₂ k₂ u t:ℝ) (hk:0≤k) (hk₂:0≤k₂) (hu:0≤u)
    (hdegree:∀a x,|(sampledColourDegree P (fun e=>(σ (Sum.inl e)).1) a x:ℝ)-
      markedExpandedPhysicalProbability p k p₂ k₂ u a*P.degree x|<t):
    (∀x,((longPhysicalStateGraph P σ {1}).degree x:ℝ)≤2*k*n+t) ∧
    (∀x,((longPhysicalStateGraph P σ {3}).degree x:ℝ)≤2*k₂*n+t) ∧
    (∀x,((longPhysicalStateGraph P σ {4}).degree x:ℝ)≤u*n+t):=by
  have hP:∀x,(P.degree x:ℝ)≤n:=by
    intro x
    exact_mod_cast (show P.degree x≤n by simpa using (P.degree_lt_card_verts x).le)
  constructor
  · intro x
    have hh:=(abs_lt.mp (hdegree 1 x)).2
    norm_num [markedExpandedPhysicalProbability] at hh
    rw [long_physical_state_singleton_degree]
    nlinarith [mul_nonneg hk (sub_nonneg.mpr (hP x))]
  constructor
  · intro x
    have hh:=(abs_lt.mp (hdegree 3 x)).2
    norm_num [markedExpandedPhysicalProbability] at hh
    rw [long_physical_state_singleton_degree]
    nlinarith [mul_nonneg hk₂ (sub_nonneg.mpr (hP x))]
  · intro x
    have hh:=(abs_lt.mp (hdegree 4 x)).2
    norm_num [markedExpandedPhysicalProbability] at hh
    rw [long_physical_state_singleton_degree]
    nlinarith [mul_nonneg hu (sub_nonneg.mpr (hP x))]
end Oberwolfach
