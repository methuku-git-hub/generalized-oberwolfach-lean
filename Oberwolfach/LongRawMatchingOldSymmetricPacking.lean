module

public import Oberwolfach.LongRawPhysicalHubRims
public import Oberwolfach.PhysicalPackingSym2Family

@[expose] public section
/-! The single selected matching packs all old symmetric edge families once
those edges have been traced to their hubs' physical rims. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawMatchingOldPackingDecEqFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_raw_matching_packs_old_symmetric_edges
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    (∀c∈M,∀c'∈M,c≠c'→Disjoint (restrictedResourceSet (mixedCandidateResources R) e c)
      (restrictedResourceSet (mixedCandidateResources R) e c'))→
    ∀old:U→Finset (Sym2 (Fin n)),
    (∀w e,e∈old w→e.toFinset∈longRawPhysicalHubRims P π d m ℓ raw g j M w)→
    ∃Pack:Finset (Sym2 (Fin n)),
      (∀w z,w≠z→Disjoint (old w) (old z)) ∧ (∀w,old w⊆Pack):=by
  intro state e R M hmatch old hcover
  exact physical_disjointness_gives_symmetric_packing old
    (longRawPhysicalHubRims P π d m ℓ raw g j M) hcover
    (long_raw_physical_hub_rims_packed P π d m ℓ raw g j M hmatch)
end Oberwolfach
