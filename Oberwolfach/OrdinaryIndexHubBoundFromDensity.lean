module

public import Oberwolfach.OrdinaryHubMarginChoice
public import Oberwolfach.OrdinaryIndexEventAbsorberHubBound

@[expose] public section
/-! Common-hub inputs for the sampled absorber from the actual index event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]
theorem ordinary_index_event_absorber_hub_bound_from_density
    (F:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (pH:ℝ)
    (j:Color) (ω smin β ε:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (hω:0<ω) (hs:0<smin) (hs1:smin≤1) (hp:smin≤pH)
    (hβ:0≤β) (hβmax:β≤ω*smin^h/4)
    (hε:0≤ε) (hεmax:ε≤smin^h/2)
    (hU:ω*Fintype.card V≤(Fintype.card U:ℝ))
    (hevent:RawOrdinaryIndices F π d h pH j (ε*Fintype.card U) σ):
    ∀ T:Finset V,T.card≤h→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
      β*Fintype.card V≤((common Finset.univ T (fun v=>Finset.univ.filter (rawWheelSpokes π d σ j v))).card:ℝ) := by
  apply ordinary_index_event_absorber_hub_bound F π d h pH j (ε*Fintype.card U) β σ hevent
  exact ordinary_hub_margin_from_density h ω smin pH β ε _ _ hω hs hs1 hp hβ hβmax hε hεmax (by positivity) hU
end Oberwolfach
