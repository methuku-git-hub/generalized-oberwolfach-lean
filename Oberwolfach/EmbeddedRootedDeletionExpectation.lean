module

public import Oberwolfach.ProfileClassEmbeddingCounts
public import Oberwolfach.RootedDeletionExpectation

@[expose] public section

/-! Root-omitted means for a class-preserving embedding of the actual
remaining populations. This applies to nested fixed-root conditioning. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V W : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
    [∀ i,Fintype (W i)] [∀ i,DecidableEq (W i)]
    {C : Type*} [Fintype C]

theorem embedded_rooted_deletion_expectation
    (e : (Σ i,W i) ↪ (Σ i,V i)) (he : ∀ v,(e v).1=v.1)
    (R : C → Finset (Σ i,V i)) (w : C → ℝ) (a : I → ℕ)
    (hR : ∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i)
    (Z : Finset (Σ i,V i)) (hrange : ∀ v,(∃ u,e u=v) ↔ v∉Z)
    (v : Σ i,V i) (m : I → ℕ)
    [∀ i,Nonempty (FixedSubset (W i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (W i)) :
    let w' := vertexRestrictedWeight R w (Z.erase v)
    (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (W i) (m i)))).expectation
      (fun σ => hypergraphWeightedDegree R
        (inducedResourceWeight R w' (insert v ((profileRootSet σ).map e))) v)=
      (∏ i,((m i).choose (a i-(if v.1=i then 1 else 0)):ℝ)/
        (Fintype.card (W i)).choose (a i-(if v.1=i then 1 else 0)))*
        hypergraphWeightedDegree R w' v := by
  have hcover (C₀) (hw : vertexRestrictedWeight R w (Z.erase v) C₀≠0) :
      ∀ x∈(R C₀).erase v,∃ u,e u=x := by
    have hd := vertexRestrictedWeight_ne_zero_disjoint R w (Z.erase v) C₀ hw
    intro x hx
    exact (hrange x).mpr (root_omitted_support_avoids (R C₀) Z v hd x hx)
  apply profile_root_weight_expectation e R (vertexRestrictedWeight R w (Z.erase v)) v
    (fun i => a i-(if v.1=i then 1 else 0)) m _ _ hm
  · intro C₀ _ hw x hx
    obtain ⟨u,rfl⟩ := hcover C₀ hw x hx
    exact Finset.mem_map.mpr ⟨u,Finset.mem_univ _,rfl⟩
  · intro C₀ hv hw i
    simpa only [hR] using profile_embedding_root_omitted_card e he (R C₀) v hv (hcover C₀ hw) i

theorem embedded_rooted_rescaled_mean_error
    (e : (Σ i,W i) ↪ (Σ i,V i)) (he : ∀ v,(e v).1=v.1)
    (R : C → Finset (Σ i,V i)) (w : C → ℝ) (a : I → ℕ)
    (hR : ∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i)
    (Z : Finset (Σ i,V i)) (hrange : ∀ v,(∃ u,e u=v) ↔ v∉Z)
    (v : Σ i,V i) (m : I → ℕ)
    [∀ i,Nonempty (FixedSubset (W i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (W i))
    (p η K δ : ℝ) (hw : ∀ C₀,0 ≤ w C₀) (hη : 0 ≤ η) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hpair : ∀ x y,x≠y → (∑ C₀,if x∈R C₀ ∧ y∈R C₀ then w C₀ else 0) ≤ K)
    (herr : ∀ x,|1-hypergraphWeightedDegree R w x| ≤ η)
    (hp : |p*(∏ i,((m i).choose (a i-(if v.1=i then 1 else 0)):ℝ)/
        (Fintype.card (W i)).choose (a i-(if v.1=i then 1 else 0)))-1| ≤ δ) :
    let w' := vertexRestrictedWeight R w (Z.erase v)
    let μ := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (W i) (m i)))
    |μ.expectation (fun σ => p*hypergraphWeightedDegree R
      (inducedResourceWeight R w' (insert v ((profileRootSet σ).map e))) v)-1| ≤
      (η+(Z.erase v).card*K)+(1+η+(Z.erase v).card*K)*δ := by
  have hload := resource_vertex_deletion_load_error R w hw K η hK hpair herr (Z.erase v) v (Finset.notMem_erase _ _)
  rw [abs_sub_comm] at hload
  have hmean := embedded_rooted_deletion_expectation e he R w a hR Z hrange v m hm
  dsimp only
  rw [finiteLaw_expectation_const_mul,hmean]
  have hh := scaled_near_unit_product_error _ _ (η+(Z.erase v).card*K) δ (by positivity) hδ hload hp
  simpa only [mul_assoc,add_assoc] using hh

end Oberwolfach
