module

public import Oberwolfach.OrdinaryTwoHubNeighbourhoodGeometry
public import Oberwolfach.OrdinarySmallRootDensity
public import Oberwolfach.DivisibilityUniformSample

@[expose] public section
/-! The actual row event gives a lower bound for every two-hub pair of
neighbourhoods, including repeated vertices and repeated hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]
theorem ordinary_dense_two_hub_geometry
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawWheelOutcome V U Γ Color)
    (p pmin smin:ℝ) (s:U→Color→ℝ) (j:Color) (α t L:ℝ)
    (hα:0≤α) (hL:0≤L)
    (hP:∀ v,(1/2+α)*Fintype.card V≤(P.degree v:ℝ)) (hF:∀ v,(F.degree v:ℝ)≤L)
    (hpmin:0<pmin) (hp:pmin≤p) (hp1:p≤1)
    (hsmin:0<smin) (hsmin1:smin≤1) (hs:∀ u,smin≤s u j)
    (hrows:RawOrdinaryRows P π d 2 Finset.univ p s j t σ):
    ∀ u u' v w,
      (pmin^2*smin^2)*(2*α)*Fintype.card V-t-2*L≤
        (((Finset.univ.filter (fun z=>rawWheelSpokes π d σ j z u ∧ rawWheelSpokes π d σ j z u'))∩
          (rawWheelGraph P σ\F).neighborFinset v∩(rawWheelGraph P σ\F).neighborFinset w).card:ℝ) := by
  apply ordinary_two_hub_neighbourhood_geometry P F π d σ p s j (2*α) (pmin^2*smin^2) t L
    (by positivity) (by positivity) hL hF
  · intro v w; exact dense_graph_common_neighbours P α hP v w
  · exact ordinary_small_root_density p pmin smin s j hpmin hp hp1 hsmin hsmin1 hs
  · exact hrows
end Oberwolfach
