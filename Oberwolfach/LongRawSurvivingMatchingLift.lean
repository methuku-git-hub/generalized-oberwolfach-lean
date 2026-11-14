module

public import Oberwolfach.LongRawSurvivingResourceState
public import Oberwolfach.LongRawFamilyFintype

@[expose] public section
/-! Preserve the same candidate identifiers and hub/length counts when the
matching selected after physical edge deletion is viewed in the raw sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_surviving_matching_lift
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (F:Finset (Sym2 (Fin n))):
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let S:=longRawSurvivingResources P π d raw g j F
    let q:=survivingCandidateEmbedding R S T (long_raw_surviving_resources_subset P π d raw g j F)
    ∀M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))),
    (∀a∈M,∀b∈M,a≠b→Disjoint
      (restrictedResourceSet R (Function.Embedding.subtype (·∈S)) a)
      (restrictedResourceSet R (Function.Embedding.subtype (·∈S)) b)) →
    (∀a∈M.map q,∀b∈M.map q,a≠b→Disjoint
      (restrictedResourceSet R (Function.Embedding.subtype (·∈T)) a)
      (restrictedResourceSet R (Function.Embedding.subtype (·∈T)) b)) ∧
    (∀(i:Option (Fin K)) (u:U),
      ((M.map q).filter (fun c=>c.val.1=i ∧ longRawSeedHub π d m ℓ c.val.1 c.val.2=u)).card =
      (M.filter (fun c=>c.val.1=i ∧ longRawSeedHub π d m ℓ c.val.1 c.val.2=u)).card) ∧
    (∀a∈M,∀z∈R a.val,∀edge,
      typedResourcePhysical π ((markedResourceTypeEquiv (V:=Fin n) (U:=U)) z)=Sum.inl edge→edge∉F) :=by
  intro R T S q M hmatch
  refine ⟨?_,?_,?_⟩
  · exact surviving_candidate_matching_lift R S T (long_raw_surviving_resources_subset P π d raw g j F) M hmatch
  · intro i u
    exact surviving_candidate_count_lift R S T (long_raw_surviving_resources_subset P π d raw g j F) M
      (fun c=>c.1=i ∧ longRawSeedHub π d m ℓ c.1 c.2=u)
  · intro a ha z hz edge he
    obtain ⟨v,hv⟩:=a.property z hz
    have hzS:z∈S:=by rw [←hv];exact v.property
    exact long_raw_surviving_resource_not_deleted P π d raw g j F z hzS edge he

theorem long_raw_lifted_matching_avoids_deleted_rims
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (F:Finset (Sym2 (Fin n))):
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let S:=longRawSurvivingResources P π d raw g j F
    let q:=survivingCandidateEmbedding R S T (long_raw_surviving_resources_subset P π d raw g j F)
    ∀M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))),
    ∀a∈M.map q,∀z∈R a.val,∀edge,
      typedResourcePhysical π ((markedResourceTypeEquiv (V:=Fin n) (U:=U)) z)=Sum.inl edge→edge∉F :=by
  intro R T S q M a ha z hz edge he
  obtain ⟨b,hb,hba⟩:=Finset.mem_map.mp ha
  subst a
  obtain ⟨v,hv⟩:=b.property z hz
  have hzS:z∈S:=by rw [←hv];exact v.property
  exact long_raw_surviving_resource_not_deleted P π d raw g j F z hzS edge he
end Oberwolfach
