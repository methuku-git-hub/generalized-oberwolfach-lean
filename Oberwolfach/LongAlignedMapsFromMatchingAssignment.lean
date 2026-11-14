module

public import Oberwolfach.LongRawSurvivingMatchingLift
public import Oberwolfach.LongRawOrdinaryComponentMapsProperty
public import Oberwolfach.LongRawAssignedComponentMapsFinal

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_aligned_maps_from_surviving_matching_assignment
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (Del:Finset (Sym2 (Fin n)))
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2):
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let S:=longRawSurvivingResources P π d raw true true Del
    let q:=survivingCandidateEmbedding R S T (long_raw_surviving_resources_subset P π d raw true true Del)
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S)))),
    (∀c∈M,∀c'∈M,c≠c'→Disjoint (restrictedResourceSet R (Function.Embedding.subtype (·∈S)) c)
      (restrictedResourceSet R (Function.Embedding.subtype (·∈S)) c'))→
    let e:=Function.Embedding.subtype (·∈T)
    let Nraw:=M.map q
    ∀(assign:LongRawSelectedOrdinary π d m ℓ e Nraw↪(Σu,(F u).ConnectedComponent)),
    (∀a,(assign a).1=(longRawSelectedOrdinaryWheel π d m ℓ e Nraw a).val.2)→
    (∀a,Fintype.card (assign a).2=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e Nraw a).1)→
    LongRawOrdinaryComponentMapsProperty F π d m ℓ e Nraw :=by
  intro R T S q M hmatch e Nraw assign hhub hsize
  have hlift:=(long_raw_surviving_matching_lift P π d m ℓ raw true true Del M hmatch).1
  exact ⟨assign,long_raw_assigned_ordinary_component_maps F hF π d m ℓ e Nraw hlift assign hhub hsize⟩
end Oberwolfach
