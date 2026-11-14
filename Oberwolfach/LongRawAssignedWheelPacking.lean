module

public import Oberwolfach.AssignedOrdinaryWheelReindex
public import Oberwolfach.RawMixedPhysicalArcHost

@[expose] public section
/-! The ordinary wheels assigned to the source cycles inherit their sampled
rim directions, spoke availability and mixed-packing disjointness. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawAssignedWheelDecEqFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_raw_assigned_wheel_packing
    {N K:ℕ} {U J:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin N)) (π:Equiv.Perm (Fin N)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin N) U Bool Bool) (g j:Bool):
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    (∀c∈M,∀c'∈M,c≠c'→Disjoint (restrictedResourceSet (mixedCandidateResources R) e c)
      (restrictedResourceSet (mixedCandidateResources R) e c'))→
    ∀(w:U) (n:J→ℕ) (select:J↪LongRawSelectedOrdinary π d m ℓ e M),
    ∀(hlen:∀z,ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M (select z)).1=n z+1),
    (∀z,(longRawSelectedOrdinaryWheel π d m ℓ e M (select z)).val.2=w)→
    let S:=longRawMarkedWheelsAtHub P π d m ℓ raw g j M w
    let r:=fun a:LongRawSelectedOrdinary π d m ℓ e M=>ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1
    let Q:=fun a:LongRawSelectedOrdinary π d m ℓ e M=>(longRawSelectedOrdinaryWheel π d m ℓ e M a).val
    let C:=reindexedOrdinaryWheel π (3*d) r Q n select hlen
    (∀z,(C z).2=w) ∧
    (∀z a,rawMarkedPairSpokes π d raw g j false ((C z).1.val a) w) ∧
    (∀z a,rawMixedPhysicalArc P π d raw ((C z).1.val a) ((C z).1.val (cycleNext a))) ∧
    (∀z z',z≠z'→Disjoint (ordinaryWheelPhysicalResources (C z)) (ordinaryWheelPhysicalResources (C z'))) ∧
    (∀z W,W∈S→Disjoint (ordinaryWheelPhysicalResources (C z)) (markedWheelPhysicalResources W)):=by
  intro state e R M hmatch w n select hlen hhub S r Q C
  have hpack:=long_raw_matching_gives_hub_packing P π d m ℓ raw g j M hmatch w
  have hs:∀a i,rawMarkedPairSpokes π d raw g j false ((Q a).1.val i) (Q a).2:=by
    intro a
    exact (long_raw_selected_ordinary_sampled_resources P π d m ℓ raw g j M a).1
  have hd:∀a i,rawMixedPhysicalArc P π d raw ((Q a).1.val i) ((Q a).1.val (cycleNext i)):=by
    intro a i
    left
    exact (long_raw_selected_ordinary_sampled_resources P π d m ℓ raw g j M a).2 i
  exact assigned_ordinary_wheels_reindex π (3*d) m _ _ _ _ _ _ r Q n select hlen w hhub hs
    (rawMixedPhysicalArc P π d raw) hd hpack.2.2.2 S hpack.2.2.1
end Oberwolfach
