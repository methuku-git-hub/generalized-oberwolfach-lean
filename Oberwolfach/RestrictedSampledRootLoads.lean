module

public import Oberwolfach.ResourceRestriction
public import Oberwolfach.ResourceRootOmittedLoads
public import Oberwolfach.BernoulliVertexSampling

@[expose] public section
/-! On a resource already present in the sampled ground set, its weighted
degree in the restricted candidate family is exactly the fixed-weight load
with that root omitted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W C:Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype C] [DecidableEq C]

theorem restricted_resource_degree_eq_root_omitted
    (R:C→Finset V) (e:W↪V) (w:C→ℝ) (v:W):
    hypergraphWeightedDegree (restrictedResourceSet R e) (fun c=>w c.val) v=
      resourceRootOmittedLoad R w (fun x=>∃ y,e y=x) (e v):=by
  rw [restricted_resource_degree]
  unfold hypergraphWeightedDegree resourceRootOmittedLoad
  apply Finset.sum_congr rfl
  intro c _
  by_cases hv:e v∈R c
  · have heq:(∀ x∈R c,∃ y,e y=x)↔(∀ x∈R c,x≠e v→∃ y,e y=x):=by
      constructor
      · intro h x hx _;exact h x hx
      · intro h x hx
        by_cases hxv:x=e v
        · exact ⟨v,hxv.symm⟩
        · exact h x hx hxv
    by_cases hs:∀ x∈R c,∃ y,e y=x
    · have ho:=heq.mp hs
      simp only [hv,if_true,true_and]
      rw [if_pos hs,if_pos ho]
    · have ho:¬(∀ x∈R c,x≠e v→∃ y,e y=x):=fun h=>hs (heq.mpr h)
      simp only [hv,if_true,true_and]
      rw [if_neg hs,if_neg ho]
  · simp [hv]

/-- For a retained root, the weighted degree is the exact root-omitted
pattern load, evaluated on the same sample and with unchanged weights. -/
theorem sampled_resource_degree_eq_pattern
    (R:C→Finset V) (w:C→ℝ) (σ:V→Bool)
    (v:{x:V // x∈bernoulliVertexSet σ}):
    hypergraphWeightedDegree
      (restrictedResourceSet R (Function.Embedding.subtype (fun x=>x∈bernoulliVertexSet σ)))
      (fun c=>w c.val) v =
      resourcePatternLoad R w (fun _ _=>true) v.val σ := by
  rw [restricted_resource_degree_eq_root_omitted]
  rw [←bernoulli_root_load_pattern]
  congr 1
  funext x
  apply propext
  constructor
  · rintro ⟨y,hy⟩
    exact hy ▸ y.property
  · intro hx
    exact ⟨⟨x,hx⟩,rfl⟩

/-- Restriction cannot increase the weighted codegree of distinct roots. -/
theorem restricted_resource_codegree_le
    (R:C→Finset V) (e:W↪V) (w:C→ℝ) (hw:∀c,0≤w c)
    (u v:W) (huv:u≠v):
    (∑c:RestrictedResource R e,
      if u∈restrictedResourceSet R e c ∧ v∈restrictedResourceSet R e c then w c.val else 0) ≤
      resourceOmittedPairWeight R w (e u) (e v) := by
  have he := Finset.sum_subtype (F:=inferInstance) (p:=fun c:C=>∀ x∈R c,∃ y,e y=x)
    (Finset.univ.filter (fun c:C=>∀ x∈R c,∃ y,e y=x)) (by intro x;simp)
    (fun c=>if e u∈R c ∧ e v∈R c then w c else 0)
  simp only [restrictedResourceSet_mem]
  rw [←he,Finset.sum_filter]
  unfold resourceOmittedPairWeight
  apply Finset.sum_le_sum
  intro c _
  have hne:e v≠e u:=fun h=>huv (e.injective h.symm)
  by_cases hu:e u∈R c <;> by_cases hv:e v∈R c
  · simp only [hu,hv,hne,true_and,ite_true]
    split_ifs <;> first | exact le_refl _ | exact hw c
  · simp [hu,hv]
  · simp [hu,hv]
  · simp [hu,hv]

end Oberwolfach
