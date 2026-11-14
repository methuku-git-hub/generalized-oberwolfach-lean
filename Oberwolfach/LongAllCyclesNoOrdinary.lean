module

public import Oberwolfach.AllLongNoShortComponents
public import Oberwolfach.LongRawComponentAssignmentFromMaps
public import Oberwolfach.LongAssignedPaddedLengths

@[expose] public section
/-! The globally assigned ordinary resources at a hub vanish when that
factor has no component of size at most K. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_all_cycles_no_ordinary_at_hub
    {n K m d:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    {X:Type} [Fintype X] [DecidableEq X]
    (F:U→SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (e:X ↪ LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m (longAssignedPaddedLength (K:=K)))) e))
    (assign:LongRawSelectedOrdinary π d m (longAssignedPaddedLength (K:=K)) e M↪(Σw,(F w).ConnectedComponent))
    (hsize:∀a,Fintype.card (assign a).2=(longAssignedPaddedLength (K:=K)) (longRawSelectedOrdinaryPayload π d m (longAssignedPaddedLength (K:=K)) e M a).1)
    (w:U) (hK:3≤K) (hAll:∀v,K<Fintype.card ((F w).connectedComponentMk v)):
    IsEmpty {a:LongRawSelectedOrdinary π d m (longAssignedPaddedLength (K:=K)) e M // (assign a).1=w}:=by
  constructor
  intro a
  cases h:assign a.val with
  | mk u C =>
    have hu:u=w:=by simpa only [h] using a.property
    subst u
    have hlong:K<Fintype.card C:=by
      induction C using SimpleGraph.ConnectedComponent.ind with
      | _ v => exact hAll v
    have hshort:Fintype.card C≤K:=by
      have hs:=hsize a.val
      rw [h] at hs
      simp only at hs
      rw [hs]
      exact long_assigned_padded_length_upper hK _
    omega
end Oberwolfach
