module

public import Oberwolfach.OrdinaryRawHubParentPrior
public import Oberwolfach.OrdinaryTriangleFiniteCoverOuterDegreeEvent

@[expose] public section
/-! The raw prior for endpoint and inner hub weights also retains the robust
    correction-star triangle cover event, on the same outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

theorem ordinary_raw_parent_and_bounded_triangle_cover_probability
    (μ:FiniteLaw (RawWheelOutcome V U Γ Color))
    (d k:ℕ) (P F:SimpleGraph V) (A:Finset V) (Z:Finset U) (π:Equiv.Perm V) (j:Color)
    (s:U→Color→ℝ) (endpointWeight:V→Sym2 (V⊕U)→ℝ) (triangleWeight:OrdinaryCycle P 3→ℝ)
    (α pstar βP ηP ηH βH c B pR pH tEndpoint tR tH κ a b e f:ℝ)
    (htri:1-a≤μ.probability (ordinaryCombinedTriangleEvent d k P F π (max (1/2) (cycleThreshold 3))
      α pstar βP ηP ηH βH c B pR pH triangleWeight j))
    (hend:1-b≤μ.probability (EndpointPhysicalPotentialEvent P F A Z Aᶜ π d j endpointWeight pR pH tEndpoint))
    (hdeep:1-e≤μ.probability (fun σ=>RawOrdinaryRows P π d 3 A pR s j tR σ ∧
      RawOrdinaryDomainIndices F π d 3 Z pH j tH σ))
    (hcover:1-f≤μ.probability (OrdinaryTriangleFiniteCoverOuterDegreeEvent κ P F Z π d j)):
    1-a-b-e-f≤μ.probability (fun σ=>
      OrdinaryRawHubParentPrior d k P F A Z π j s endpointWeight triangleWeight
        α pstar βP ηP ηH βH c B pR pH tEndpoint tR tH σ ∧
      OrdinaryTriangleFiniteCoverOuterDegreeEvent κ P F Z π d j σ):=by
  have hprior:=ordinary_raw_hub_parent_prior_probability μ d k P F A Z π j s endpointWeight triangleWeight
    α pstar βP ηP ηH βH c B pR pH tEndpoint tR tH a b e htri hend hdeep
  have hi:=finiteLaw_intersection_lower μ _ _ (a+b+e) f (by linarith) hcover
  convert hi using 1 <;> ring
end Oberwolfach
