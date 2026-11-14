module

public import Oberwolfach.OrdinaryCombinedTriangleEvent
public import Oberwolfach.EndpointPhysicalPotentialEvent
public import Oberwolfach.RawOrdinaryRowEvent
public import Oberwolfach.RawOrdinaryDomainIndexEvent
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! The full-host triangle event, fixed endpoint potentials and deeper
inner row/column profiles on the same original raw outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def OrdinaryRawHubParentPrior
    (d k:ℕ) (P F:SimpleGraph V) (A:Finset V) (Z:Finset U) (π:Equiv.Perm V) (j:Color)
    (s:U→Color→ℝ) (endpointWeight:V→Sym2 (V⊕U)→ℝ) (triangleWeight:OrdinaryCycle P 3→ℝ)
    (α pstar βP ηP ηH βH c B pR pH tEndpoint tR tH:ℝ)
    (σ:RawWheelOutcome V U Γ Color):Prop :=
  ordinaryCombinedTriangleEvent d k P F π (max (1/2) (cycleThreshold 3)) α pstar βP ηP ηH βH c B pR pH triangleWeight j σ ∧
  EndpointPhysicalPotentialEvent P F A Z Aᶜ π d j endpointWeight pR pH tEndpoint σ ∧
  RawOrdinaryRows P π d 3 A pR s j tR σ ∧
  RawOrdinaryDomainIndices F π d 3 Z pH j tH σ

theorem ordinary_raw_hub_parent_prior_probability
    (μ:FiniteLaw (RawWheelOutcome V U Γ Color))
    (d k:ℕ) (P F:SimpleGraph V) (A:Finset V) (Z:Finset U) (π:Equiv.Perm V) (j:Color)
    (s:U→Color→ℝ) (endpointWeight:V→Sym2 (V⊕U)→ℝ) (triangleWeight:OrdinaryCycle P 3→ℝ)
    (α pstar βP ηP ηH βH c B pR pH tEndpoint tR tH a b e:ℝ)
    (htri:1-a≤μ.probability (ordinaryCombinedTriangleEvent d k P F π (max (1/2) (cycleThreshold 3))
      α pstar βP ηP ηH βH c B pR pH triangleWeight j))
    (hend:1-b≤μ.probability (EndpointPhysicalPotentialEvent P F A Z Aᶜ π d j endpointWeight pR pH tEndpoint))
    (hdeep:1-e≤μ.probability (fun σ=>RawOrdinaryRows P π d 3 A pR s j tR σ ∧
      RawOrdinaryDomainIndices F π d 3 Z pH j tH σ)) :
    1-a-b-e≤μ.probability (OrdinaryRawHubParentPrior d k P F A Z π j s endpointWeight triangleWeight
      α pstar βP ηP ηH βH c B pR pH tEndpoint tR tH) := by
  have h1:=finiteLaw_intersection_lower μ _ _ a b htri hend
  have h2:=finiteLaw_intersection_lower μ _ _ (a+b) e (by linarith) hdeep
  have hn : 1-a-b-e = 1-(a+b)-e := by ring
  rw [hn]
  apply h2.trans
  apply finiteLaw_probability_mono
  intro σ h
  exact ⟨h.1.1,h.1.2,h.2.1,h.2.2⟩
end Oberwolfach
