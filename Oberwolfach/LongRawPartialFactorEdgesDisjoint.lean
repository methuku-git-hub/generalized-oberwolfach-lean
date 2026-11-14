module

public import Oberwolfach.LongRawSelectedRimEdgesDisjoint
public import Oberwolfach.PartialFactorEdgeDisjointness

@[expose] public section
/-! Partial factors covered by a raw ordinary resource matching have
pairwise disjoint physical edge images at different hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_partial_factor_edges_disjoint
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    (∀c∈M,∀c'∈M,c≠c'→Disjoint (restrictedResourceSet (mixedCandidateResources R) e c)
      (restrictedResourceSet (mixedCandidateResources R) e c')) →
    ∀(D:U→Type) (F:∀u,SimpleGraph (D u)) (ψ:∀u,D u→Fin n),
    (∀u x y,(F u).Adj x y→∃a:LongRawSelectedOrdinary π d m ℓ e M,
      (longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2=u ∧
      longRawSelectedRimRelation π d m ℓ e M a (ψ u x) (ψ u y)) →
    ∀u v,u≠v→Disjoint (partialFactorPhysicalEdges (D u) (F u) (ψ u))
      (partialFactorPhysicalEdges (D v) (F v) (ψ v)) :=by
  intro state e R M hmatch D F ψ hcover
  apply partial_factors_physical_edges_disjoint D F ψ
    (fun a:LongRawSelectedOrdinary π d m ℓ e M=>(longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2)
    (longRawSelectedRimEdges π d m ℓ e M)
  · exact long_raw_selected_rim_edges_disjoint P π d m ℓ raw g j M hmatch
  · intro u x y hxy
    obtain ⟨a,hu,hrim⟩:=hcover u x y hxy
    exact ⟨a,hu,long_raw_selected_rim_relation_edge_mem π d m ℓ e M a _ _ hrim⟩
end Oberwolfach
