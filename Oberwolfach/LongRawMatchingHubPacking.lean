module

public import Oberwolfach.LongRawSelectedMixedPhysicalDisjoint
public import Oberwolfach.LongRawSelectedOrdinarySampledResources

@[expose] public section
/-! Extract the actual marked packing at one hub from the original mixed
matching, while keeping physical disjointness from its ordinary wheels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawHubPackingDecEqFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

def longRawMarkedWheelsAtHub
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),U→
      Finset (LongRawRealizedWheel P π d m raw g j ℓ none):=by
  classical
  intro state e M w
  exact (Finset.univ.filter (fun a:LongRawSelectedMarked π d m ℓ e M=>
    (longRawSelectedMarkedWheel P π d m ℓ raw g j M a).2.val=w)).image
      (longRawSelectedMarkedWheel P π d m ℓ raw g j M)

theorem long_raw_matching_gives_hub_packing
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    (∀c∈M,∀c'∈M,c≠c'→Disjoint (restrictedResourceSet (mixedCandidateResources R) e c)
      (restrictedResourceSet (mixedCandidateResources R) e c'))→
    ∀w:U,
    let S:=longRawMarkedWheelsAtHub P π d m ℓ raw g j M w
    (∀W∈S,W.2.val=w) ∧
    (∀W∈S,∀Z∈S,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z)) ∧
    (∀a:LongRawSelectedOrdinary π d m ℓ e M,∀W∈S,
      Disjoint (ordinaryWheelPhysicalResources (longRawSelectedOrdinaryWheel π d m ℓ e M a).val) (markedWheelPhysicalResources W)) ∧
    (∀a a':LongRawSelectedOrdinary π d m ℓ e M,a≠a'→
      Disjoint (ordinaryWheelPhysicalResources (longRawSelectedOrdinaryWheel π d m ℓ e M a).val)
        (ordinaryWheelPhysicalResources (longRawSelectedOrdinaryWheel π d m ℓ e M a').val)):=by
  classical
  intro state e R M hmatch w S
  have hm:=long_raw_selected_mixed_physical_disjoint P π d m ℓ raw g j M hmatch
  have hEq:longRawHubPackingDecEqFin n=instDecidableEqFin n:=Subsingleton.elim _ _
  rw [hEq] at hmatch
  have ho:=long_raw_selected_ordinary_physical_disjoint P π d m ℓ raw g j M hmatch
  constructor
  · intro W hW
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hW
    exact (Finset.mem_filter.mp ha).2
  constructor
  · intro W hW Z hZ hne
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hW
    obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp hZ
    exact hm.1 a b (fun he=>hne (congrArg (longRawSelectedMarkedWheel P π d m ℓ raw g j M) he))
  constructor
  · intro a W hW
    obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp hW
    exact (hm.2 b a).symm
  · exact ho
end Oberwolfach
