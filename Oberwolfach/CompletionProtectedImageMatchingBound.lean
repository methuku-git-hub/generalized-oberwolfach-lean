module

public import Oberwolfach.CompletionProtectedDomainForcedImages
public import Oberwolfach.PrescribedTargetMatching

@[expose] public section
/-! The completion image inside a protected set is controlled by the
prescribed sources and twice the number of assigned matching edges. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem prescribed_matching_endpoints_card_le_twice
    {V:Type} [DecidableEq V] (M:Finset (V×V)):
    (prescribedMatchingEndpoints M).card≤2*M.card :=by
  have heq:prescribedMatchingEndpoints M=M.image Prod.fst∪M.image Prod.snd:=by
    ext x
    simp only [prescribedMatchingEndpoints,Finset.mem_biUnion,Finset.mem_insert,
      Finset.mem_singleton,Finset.mem_union,Finset.mem_image]
    constructor
    · rintro ⟨e,he,hx|hx⟩
      · exact Or.inl ⟨e,he,hx.symm⟩
      · exact Or.inr ⟨e,he,hx.symm⟩
    · rintro (⟨e,he,hx⟩|⟨e,he,hx⟩)
      · exact ⟨e,he,Or.inl hx.symm⟩
      · exact ⟨e,he,Or.inr hx.symm⟩
  rw [heq]
  have h:=Finset.card_union_le (M.image Prod.fst) (M.image Prod.snd)
  have h₁:=Finset.card_image_le (s:=M) (f:=Prod.fst)
  have h₂:=Finset.card_image_le (s:=M) (f:=Prod.snd)
  omega

theorem completion_protected_image_matching_bound
    {X V:Type} [Fintype X] [DecidableEq X] [DecidableEq V]
    (I:Finset V) (B:Finset X) (Φ g:X→V) (Lists Pre Required:Finset V)
    (M:Finset (V×V))
    (hfixed:∀x∈B,Φ x=g x) (hfree:∀x,x∉B→Φ x∈Lists)
    (havoid:Disjoint Lists I)
    (hforced:B.image g=Pre∪prescribedMatchingEndpoints M∪Required):
    (((Finset.univ.image Φ)∩I).card)≤Pre.card+2*M.card+Required.card :=by
  have h:=completion_protected_domain_forced_images I B Φ g Lists Pre
    (prescribedMatchingEndpoints M) Required hfixed hfree havoid hforced
  have hp:=Finset.card_le_card (Finset.inter_subset_left (s₁:=Pre) (s₂:=I))
  have hm:=Finset.card_le_card (Finset.inter_subset_left (s₁:=prescribedMatchingEndpoints M) (s₂:=I))
  have hr:=Finset.card_le_card (Finset.inter_subset_left (s₁:=Required) (s₂:=I))
  have he:=prescribed_matching_endpoints_card_le_twice M
  omega
end Oberwolfach
