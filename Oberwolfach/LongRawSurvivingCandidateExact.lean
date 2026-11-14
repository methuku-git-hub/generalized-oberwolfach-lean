module

public import Oberwolfach.LongRawSurvivingResourceExact
public import Oberwolfach.LongRawSurvivingMatchingLift
public import Oberwolfach.RestrictedResourceStateExact

@[expose] public section
/-! A raw wheel survives exactly when none of its physical rim edges is
deleted; the original typed coordinates and spokes are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_surviving_candidate_iff
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (F:Finset (Sym2 (Fin n))):
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let S:=longRawSurvivingResources P π d raw g j F
    let q:=survivingCandidateEmbedding R S T (long_raw_surviving_resources_subset P π d raw g j F)
    ∀a:RestrictedResource R (Function.Embedding.subtype (·∈T)),
      (∃b,q b=a) ↔ ∀z∈R a.val,∀edge,
        typedResourcePhysical π ((markedResourceTypeEquiv (V:=Fin n) (U:=U)) z)=Sum.inl edge→edge∉F :=by
  intro R T S q a
  rw [surviving_candidate_lift_range_iff]
  constructor
  · intro h z hz edge he
    exact long_raw_surviving_resource_not_deleted P π d raw g j F z (h hz) edge he
  · intro h z hz
    apply (long_raw_surviving_resource_iff P π d raw g j F z).mpr
    constructor
    · obtain ⟨v,hv⟩:=a.property z hz
      rw [←hv]
      exact v.property
    · exact h z hz
end Oberwolfach
