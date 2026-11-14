module

public import Oberwolfach.LongRawSelectedWheelRimCoverage
public import Oberwolfach.LongRawMatchingHubPacking
public import Oberwolfach.AssignedOrdinaryWheelReindex

@[expose] public section
/-! The actual hub packing and its reindexed assigned ordinary wheels use
only the matching's physical rim resources at that hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawHubWheelRimDecEqFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_raw_hub_marked_rims_covered
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),∀w W,
      W∈longRawMarkedWheelsAtHub P π d m ℓ raw g j M w→
      markedCyclePhysicalEdges _ _ _ _ m π (3*d) W.1⊆longRawPhysicalHubRims P π d m ℓ raw g j M w:=by
  intro state e R M w W hW x hx
  unfold longRawMarkedWheelsAtHub at hW
  obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hW
  have hub: (longRawSelectedMarkedWheel P π d m ℓ raw g j M a).2.val=w:=(Finset.mem_filter.mp ha).2
  have hh:=(long_raw_selected_wheel_rims_covered P π d m ℓ raw g j M).1 a x hx
  simpa only [hub] using hh

theorem reindexed_ordinary_rim_covered
    {V U A J:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    (π:Equiv.Perm V) (b:ℕ) (r:A→ℕ) (Q:∀a,OrderedOrdinaryWheel (U:=U) π b (r a))
    (n:J→ℕ) (select:J→A) (hlen:∀j,r (select j)=n j+1) (Pack:Finset (Finset V))
    (hQ:∀j (i:Fin (r (select j))),{(Q (select j)).1.val i,(Q (select j)).1.val (cycleNext i)}∈Pack):
    ∀j (i:Fin (n j+1)),
      {(reindexedOrdinaryWheel π b r Q n select hlen j).1.val i,
       (reindexedOrdinaryWheel π b r Q n select hlen j).1.val (cycleNext i)}∈Pack:=by
  intro j i
  dsimp only [reindexedOrdinaryWheel]
  rw [cast_ordinary_wheel_vertex,cast_ordinary_wheel_vertex,cycleNext_cast (hlen j) i]
  exact hQ j _
end Oberwolfach
