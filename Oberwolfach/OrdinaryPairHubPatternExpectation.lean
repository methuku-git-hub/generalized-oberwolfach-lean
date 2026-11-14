module

public import Oberwolfach.OrdinaryPairHubIndependence

@[expose] public section

/-! Factor the omitted-root candidate event under any product law on the
original raw coordinate types. No marginal values are assumed here. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_pair_hub_pattern_load_expectation
    (P F:SimpleGraph V) (π:Equiv.Perm V) (r d:ℕ)
    (hF:permutationConflictGraph π (3*d)≤F)
    (w:OrdinaryWheel P F (fun (_:V) (_:Unit)=>True) r→ℝ)
    (μ:∀ e:RawWheelCoordinate V U,FiniteLaw (RawWheelCoordinateState Γ Color e))
    (j:Color) (u u':U) (root:Sym2 V⊕(V×Unit)):
    (FiniteLaw.pi μ).expectation (fun σ=>
      resourcePatternLoad ordinaryWheelResources w (fun _ _=>true) root
        (ordinaryResourceState (rawWheelGraph P σ) (ordinaryPairHubSpokes π d σ j u u')))=
      ∑ W,(if root∈ordinaryWheelResources W then w W else 0)*
        ∏ a∈ordinaryWheelResources W\{root},(FiniteLaw.pi μ).probability (fun σ=>
          ordinaryResourceState (rawWheelGraph P σ) (ordinaryPairHubSpokes π d σ j u u') a=true) := by
  exact resourcePatternLoad_supported_expectation
    (E:=RawWheelCoordinate V U) (A:=Sym2 V⊕(V×Unit))
    (I:=OrdinaryWheel P F (fun (_:V) (_:Unit)=>True) r) (State:=fun _=>Bool) μ ordinaryWheelResources w
    (fun _ _=>true) (ordinaryPairHubCoordinates π d u u')
    (fun σ=>ordinaryResourceState (rawWheelGraph P σ) (ordinaryPairHubSpokes π d σ j u u'))
    (ordinary_pair_hub_resource_supported P π d j u u') root
    (by
      intro W _ a ha b hb hab
      exact ordinary_pair_hub_candidate_coordinates_disjoint P F π d r hF W u u' a b
        (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp hb).1 hab)
end Oberwolfach
