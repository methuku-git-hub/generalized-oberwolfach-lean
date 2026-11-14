module

public import Oberwolfach.LongRawIncidenceFamily
public import Oberwolfach.LongRawPhysicalResidualAfterDeletion

@[expose] public section
/-! A physical rim endpoint is a raw endpoint, or the image of one under π. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_raw_physical_incidence_subset_two_raw
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P D:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let S:=longRawSurvivingResources P π d raw g j D.edgeFinset
    let f:=survivingResourceEmbedding S T (long_raw_surviving_resources_subset P π d raw g j D.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j
    ∀x,rimIncidentResources (f.trans φ) x⊆
      longRawIncidenceSet S (.inl x) ∪ longRawIncidenceSet S (.inl (π.symm x)):=by
  intro T S f φ x z hz
  have hez:∃y,y≠x ∧ (f.trans φ) z=Sum.inl s(x,y):=by
    simpa only [rimIncidentResources,Finset.mem_filter,Finset.mem_univ,true_and] using hz
  obtain ⟨y,hy,he⟩:=hez
  change typedResourcePhysical π ((markedResourceTypeEquiv (V:=Fin n) (U:=U)) z.val)=Sum.inl s(x,y) at he
  cases h:z.val with
  | inr spoke => simp [markedResourceTypeEquiv,typedResourcePhysical,h] at he
  | inl rim =>
    cases rim with
    | inl e =>
      rcases e with ⟨v,w⟩
      have hp:s(v,w)=s(x,y):=by simpa [markedResourceTypeEquiv,typedResourcePhysical,h] using he
      have hh:=Sym2.eq_iff.mp hp
      apply Finset.mem_union_left
      simp only [longRawIncidenceSet,Finset.mem_filter,Finset.mem_univ,true_and,longRawResourceIncident,h]
      rcases hh with h1|h1
      · exact Or.inl h1.1
      · exact Or.inr h1.2
    | inr e =>
      rcases e with ⟨v,w⟩
      have hp:s(v,π w)=s(x,y):=by simpa [markedResourceTypeEquiv,typedResourcePhysical,h] using he
      have hh:=Sym2.eq_iff.mp hp
      rcases hh with h1|h1
      · apply Finset.mem_union_left
        simp only [longRawIncidenceSet,Finset.mem_filter,Finset.mem_univ,true_and,longRawResourceIncident,h]
        exact Or.inl h1.1
      · apply Finset.mem_union_right
        simp only [longRawIncidenceSet,Finset.mem_filter,Finset.mem_univ,true_and,longRawResourceIncident,h]
        right
        apply π.injective
        simpa using h1.2
end Oberwolfach
