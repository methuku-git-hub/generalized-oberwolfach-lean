module

public import Oberwolfach.LongRawSurvivingResourceExact
public import Oberwolfach.ResourceRootOmittedLoads

@[expose] public section
/-! Deleting physical rims changes a fixed-weight root-omitted load by at
most the sum of the original pair weights of the realised deleted resources.
The estimate is simultaneous for every root and every later deletion set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U I:Type} [Fintype U] [DecidableEq U] [Fintype I]

theorem long_raw_adaptive_omitted_load_after_rim_deletion
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool)
    (R:I→Finset (LongRawHubResource n U)) (w:I→ℝ) (hw:∀i,0≤w i)
    (F:Finset (Sym2 (Fin n))) (root:LongRawHubResource n U):
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let S:=longRawSurvivingResources P π d raw g j F
    let Deleted:=T.filter (fun z=>∃edge,typedResourcePhysical π
      ((markedResourceTypeEquiv (V:=Fin n) (U:=U)) z)=Sum.inl edge ∧ edge∈F)
    |resourceRootOmittedLoad R w (·∈S) root-resourceRootOmittedLoad R w (·∈T) root|≤
      ∑z∈Deleted,resourceOmittedPairWeight R w root z :=by
  intro T S Deleted
  have hb:=resourceRootOmittedLoad_change R w hw (·∈T) (·∈S) root
  have he:∀z, ¬(z∈T ↔ z∈S) ↔ z∈Deleted:=by
    intro z
    have hst:S⊆T:=long_raw_surviving_resources_subset P π d raw g j F
    have hs:=long_raw_surviving_resource_iff P π d raw g j F z
    dsimp [Deleted]
    rw [Finset.mem_filter]
    constructor
    · intro h
      have ht:z∈T:=by
        by_contra ht
        have hnot:z∉S:=fun hS=>ht (hst hS)
        exact h ⟨fun hT=>False.elim (ht hT),fun hS=>False.elim (hnot hS)⟩
      have hn:z∉S:=by
        intro hS
        exact h ⟨fun _=>hS,fun _=>ht⟩
      refine ⟨ht,?_⟩
      have hh:¬(∀edge,typedResourcePhysical π ((markedResourceTypeEquiv (V:=Fin n) (U:=U)) z)=Sum.inl edge→edge∉F):=by
        intro hgood
        exact hn (hs.mpr ⟨ht,hgood⟩)
      push_neg at hh
      exact hh
    · rintro ⟨ht,edge,he,hF⟩ heq
      have hS:=heq.mp ht
      have hgood:∀edge,typedResourcePhysical π ((markedResourceTypeEquiv (V:=Fin n) (U:=U)) z)=Sum.inl edge→edge∉F:=(hs.mp hS).2
      exact hgood edge he hF
  simpa only [he, Finset.sum_ite_mem, Finset.univ_inter] using hb
end Oberwolfach
