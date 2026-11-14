module

public import Oberwolfach.LongRawSelectedRimEdges
public import Oberwolfach.LongRawSelectedOrdinaryPhysicalDisjoint

@[expose] public section
/-! Distinct selected ordinary wheels have disjoint physical rim edges,
including when their hubs differ. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_selected_rim_edges_disjoint
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    (∀c∈M,∀c'∈M,c≠c'→Disjoint (restrictedResourceSet (mixedCandidateResources R) e c)
      (restrictedResourceSet (mixedCandidateResources R) e c')) →
    ∀a a':LongRawSelectedOrdinary π d m ℓ e M,a≠a'→
      Disjoint (longRawSelectedRimEdges π d m ℓ e M a) (longRawSelectedRimEdges π d m ℓ e M a') :=by
  intro state e R M hmatch a a' hne
  have hP:=long_raw_selected_ordinary_physical_disjoint P π d m ℓ raw g j M hmatch a a' hne
  apply Finset.disjoint_left.mpr
  intro edge ha hb
  have h₁:=long_raw_selected_rim_edge_is_physical_resource π d m ℓ e M a edge ha
  have h₂:=long_raw_selected_rim_edge_is_physical_resource π d m ℓ e M a' edge hb
  exact (Finset.disjoint_left.mp hP) h₁ h₂
end Oberwolfach
