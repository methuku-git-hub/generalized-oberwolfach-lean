module

public import Oberwolfach.RootOmittedClassCounts
public import Oberwolfach.RootedProfileExpectation

@[expose] public section

/-! Actual root-omitted expectations after deleting the other fixed
vertices. The original cycle identifiers and surviving weights are
unchanged, and the profile loses one label only in the root's class. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
    {C : Type*} [Fintype C]

theorem vertexRestrictedWeight_ne_zero_disjoint {W : Type*} [DecidableEq W]
    (R : C → Finset W) (w : C → ℝ) (Z : Finset W) (C₀ : C)
    (h : vertexRestrictedWeight R w Z C₀≠0) : Disjoint (R C₀) Z := by
  by_contra hd
  simp only [vertexRestrictedWeight,hd,ite_false,ne_eq,not_true_eq_false] at h

theorem rooted_deletion_profile_expectation
    (R : C → Finset (Σ i,V i)) (w : C → ℝ) (a : I → ℕ)
    (hR : ∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i)
    (Z : Finset (Σ i,V i)) (v : Σ i,V i) (m : I → ℕ)
    [∀ i,Nonempty (FixedSubset (ProfileRemainingClass Z i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (ProfileRemainingClass Z i)) :
    let w' := vertexRestrictedWeight R w (Z.erase v)
    (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (ProfileRemainingClass Z i) (m i)))).expectation
      (fun σ => hypergraphWeightedDegree R
        (inducedResourceWeight R w' (insert v ((profileRootSet σ).map (profileComplementEmbedding Z)))) v)=
      (∏ i,((m i).choose (a i-(if v.1=i then 1 else 0)):ℝ)/
        (Fintype.card (ProfileRemainingClass Z i)).choose (a i-(if v.1=i then 1 else 0)))*
        hypergraphWeightedDegree R w' v := by
  apply profile_root_weight_expectation (profileComplementEmbedding Z) R
    (vertexRestrictedWeight R w (Z.erase v)) v (fun i => a i-(if v.1=i then 1 else 0)) m _ _ hm
  · intro C₀ hv hw x hx
    have hd := vertexRestrictedWeight_ne_zero_disjoint R w (Z.erase v) C₀ hw
    have hz := root_omitted_support_avoids (R C₀) Z v hd x hx
    obtain ⟨y,hy⟩ := (profileComplementEmbedding_range Z x).mpr hz
    exact Finset.mem_map.mpr ⟨y,Finset.mem_univ _,hy⟩
  · intro C₀ hv hw i
    have hd := vertexRestrictedWeight_ne_zero_disjoint R w (Z.erase v) C₀ hw
    simpa only [hR] using root_omitted_preimage_class_card (R C₀) Z v hv hd i

theorem rooted_deletion_rescaled_mean_error
    (R : C → Finset (Σ i,V i)) (w : C → ℝ) (a : I → ℕ)
    (hR : ∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i)
    (Z : Finset (Σ i,V i)) (v : Σ i,V i) (m : I → ℕ)
    [∀ i,Nonempty (FixedSubset (ProfileRemainingClass Z i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (ProfileRemainingClass Z i))
    (p η K δ : ℝ) (hw : ∀ C₀,0 ≤ w C₀) (hη : 0 ≤ η) (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (hpair : ∀ x y,x≠y → (∑ C₀,if x∈R C₀ ∧ y∈R C₀ then w C₀ else 0) ≤ K)
    (herr : ∀ x,|1-hypergraphWeightedDegree R w x| ≤ η)
    (hp : |p*(∏ i,((m i).choose (a i-(if v.1=i then 1 else 0)):ℝ)/
        (Fintype.card (ProfileRemainingClass Z i)).choose (a i-(if v.1=i then 1 else 0)))-1| ≤ δ) :
    let w' := vertexRestrictedWeight R w (Z.erase v)
    let μ := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (ProfileRemainingClass Z i) (m i)))
    |μ.expectation (fun σ => p*hypergraphWeightedDegree R
      (inducedResourceWeight R w' (insert v ((profileRootSet σ).map (profileComplementEmbedding Z)))) v)-1| ≤
      (η+(Z.erase v).card*K)+(1+η+(Z.erase v).card*K)*δ := by
  have hload := resource_vertex_deletion_load_error R w hw K η hK hpair herr (Z.erase v) v (Finset.notMem_erase _ _)
  rw [abs_sub_comm] at hload
  have hmean := rooted_deletion_profile_expectation R w a hR Z v m hm
  dsimp only
  rw [finiteLaw_expectation_const_mul,hmean]
  have hh := scaled_near_unit_product_error _ _ (η+(Z.erase v).card*K) δ (by positivity) hδ hload hp
  simpa only [mul_assoc,add_assoc] using hh

end Oberwolfach
