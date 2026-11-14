module

public import Oberwolfach.LongAssignedMixedTargetProfile
public import Oberwolfach.LongMixedHubSpokeCounts

@[expose] public section
/-! On an ordinary spoke root at a fixed hub, the source target equals
that hub's prescribed ordinary coefficient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_ordinary_hub_root_target
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (m:ℕ) (θ D p k:ℝ) (i:Fin K) (u:U)
    (z:((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))
    (hz:z∈ordinaryCommonHubSpokeRoots u):
    longAssignedMixedTarget F hF K m θ D p k (some i) z=
      longAssignedKeptOrdinaryContribution F hF K θ i u/
        longAssignedApproxOrdinaryWeight F hF K m θ u:=by
  simp only [ordinaryCommonHubSpokeRoots,Finset.mem_map,ordinaryHubSpokeRoots,
    Finset.mem_image,Finset.mem_univ,true_and] at hz
  obtain ⟨x,⟨v,rfl⟩,rfl⟩:=hz
  rfl
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_ordinary_hub_root_load_bound
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (m:ℕ) (θ D p k t τ:ℝ) (hτ:0≤τ) (i:Fin K) (u:U)
    {C:Type} [Fintype C]
    (R:C→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (w:C→ℝ) (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (hη:longAssignedKeptOrdinaryContribution F hF K θ i u/
      longAssignedApproxOrdinaryWeight F hF K m θ u≤4)
    (hload:∀z,state z=true→
      |resourcePatternLoad R w (fun _ _=>true) z state-longAssignedMixedTarget F hF K m θ D p k (some i) z|≤
        t+τ*longAssignedMixedTarget F hF K m θ D p k (some i) z):
    ∀z∈ordinaryCommonHubSpokeRoots u,state z=true→
      |resourcePatternLoad R w (fun _ _=>true) z state-
        longAssignedKeptOrdinaryContribution F hF K θ i u/
          longAssignedApproxOrdinaryWeight F hF K m θ u|≤t+4*τ :=by
  intro z hz hs
  have h:=hload z hs
  rw [long_ordinary_hub_root_target F hF m θ D p k i u z hz] at h
  have hh:=mul_le_mul_of_nonneg_left hη hτ
  linarith
end Oberwolfach
