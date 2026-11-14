module

public import Oberwolfach.ExpandedRawMarkedPositiveSupportAnyStage
public import Oberwolfach.MarkedExpandedApproximateProjection
public import Oberwolfach.FiniteLawSupportProbabilityMono

@[expose] public section
/-! Add positivity at active approximate marked spokes without changing the
probability of any event on the expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [Nonempty V] [LinearOrder V] [DecidableEq U]

theorem expanded_approximate_positive_spokes_on_event
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (p k p₂ k₂ u₀:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu₀:0≤u₀)
    (hsum:2*p+2*k+2*p₂+2*k₂+u₀≤1)
    (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀ω,Fintype (R ω)] (ν:∀ω,FiniteLaw (R ω))
    (E:(Σω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e,R ω)→Prop):
    let μ:=(FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V)
      p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum d hd q hq hQ s hs hS)).sigma ν;
    μ.probability E≤μ.probability (fun z=>E z ∧
      ∀g j v u,rawMarkedPairSpokes π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) g j true v u→q u g≠0) :=by
  intro μ
  apply finiteLaw_probability_mono_on_support μ E _
  intro z hz hE
  refine ⟨hE,?_⟩
  intro g j v u hspoke
  have hh:rawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g j true v u:=by
    simpa only [rawMarkedPairSpokes,rawExpandedApproximateCollapse,id_eq] using hspoke
  exact ne_of_gt (expanded_raw_marked_spoke_positive_density_any_stage π d hd p k p₂ k₂ u₀ hp hk hp₂ hk₂ hu₀ hsum q hq hQ s hs hS ν z hz g j v u hh)
end Oberwolfach
