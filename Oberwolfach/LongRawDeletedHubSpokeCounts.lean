module

public import Oberwolfach.LongRawSurvivingStateIdentity
public import Oberwolfach.LongRawOrdinaryHubCount

@[expose] public section
/-! Physical rim deletion does not alter any of the actual ordinary hub
spoke-root counts used in the retained-frequency tests. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_ordinary_hub_spoke_state_after_rim_deletion
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (F:Finset (Sym2 (Fin n)))
    (u:U) (z:LongRawHubResource n U) (hz:z∈ordinaryCommonHubSpokeRoots u):
    longRawHubState P π d (rawMarkedDeleteRims raw F) g j z=longRawHubState P π d raw g j z :=by
  simp only [ordinaryCommonHubSpokeRoots,Finset.mem_map,ordinaryHubSpokeRoots,
    Finset.mem_image,Finset.mem_univ,true_and] at hz
  obtain ⟨x,⟨v,rfl⟩,rfl⟩:=hz
  rfl

theorem long_raw_ordinary_hub_spoke_count_after_rim_deletion
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (F:Finset (Sym2 (Fin n)))
    (u:U):
    ((ordinaryCommonHubSpokeRoots u).filter (fun z=>longRawHubState P π d (rawMarkedDeleteRims raw F) g j z=true)).card=
      ((ordinaryCommonHubSpokeRoots u).filter (fun z=>longRawHubState P π d raw g j z=true)).card :=by
  congr 1
  apply Finset.ext
  intro z
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hz,h⟩
    exact ⟨hz,(long_raw_ordinary_hub_spoke_state_after_rim_deletion P π d raw g j F u z hz) ▸ h⟩
  · rintro ⟨hz,h⟩
    exact ⟨hz,(long_raw_ordinary_hub_spoke_state_after_rim_deletion P π d raw g j F u z hz).symm ▸ h⟩
end Oberwolfach
