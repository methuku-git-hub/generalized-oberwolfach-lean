module

public import Oberwolfach.EmbeddedProfileSampling

@[expose] public section

/-! Expected weighted degree at one specified root. Only the root is
omitted from the inclusion test; zeroed resources may lie outside the
sampling populations. All nonzero weights remain the supplied weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
    {W C : Type*} [DecidableEq W] [Fintype C]

theorem embedded_profile_weighted_support_expectation (e : (Σ i,V i) ↪ W)
    (F : C → Finset W) (w : C → ℝ) (a m : I → ℕ)
    (hF : ∀ C₀,w C₀≠0 → F C₀⊆Finset.univ.map e)
    (ha : ∀ C₀,w C₀≠0 → ∀ i,(Finset.univ.filter (fun v : V i => e ⟨i,v⟩∈F C₀)).card=a i)
    [∀ i,Nonempty (FixedSubset (V i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (V i)) :
    (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))).expectation
      (fun σ => ∑ C₀,if F C₀⊆(profileRootSet σ).map e then w C₀ else 0)=
      (∏ i,((m i).choose (a i):ℝ)/(Fintype.card (V i)).choose (a i))*(∑ C₀,w C₀) := by
  rw [finiteLaw_expectation_sum]
  have hp (C₀ : C) :
      (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))).expectation
        (fun σ => if F C₀⊆(profileRootSet σ).map e then w C₀ else 0)=
      w C₀*(∏ i,((m i).choose (a i):ℝ)/(Fintype.card (V i)).choose (a i)) := by
    by_cases hw : w C₀=0
    · simp only [hw,ite_self,finiteLaw_expectation_const,zero_mul]
    · rw [finiteLaw_expectation_indicator_value]
      have hh := embedded_profile_inclusion_probability e ∅ (F C₀)
        (by simpa only [Finset.empty_union] using hF C₀ hw) m hm
      have hprob : (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))).probability
          (fun σ => F C₀⊆(profileRootSet σ).map e)=
          ∏ i,((m i).choose (a i):ℝ)/(Fintype.card (V i)).choose (a i) := by
        simpa only [Finset.empty_union,Finset.notMem_empty,not_false_eq_true,and_true,ha C₀ hw] using hh
      rw [hprob]
  simp_rw [hp]
  rw [← Finset.sum_mul,mul_comm]

theorem induced_root_degree_sum [Fintype W]
    (R : C → Finset W) (w : C → ℝ) (v : W) (A : Finset W) :
    hypergraphWeightedDegree R (inducedResourceWeight R w (insert v A)) v=
      ∑ C₀,if (R C₀).erase v⊆A then (if v∈R C₀ then w C₀ else 0) else 0 := by
  unfold hypergraphWeightedDegree
  apply Finset.sum_congr rfl
  intro C₀ _
  have hsub : (R C₀).erase v⊆A ↔ R C₀⊆insert v A := by
    constructor
    · intro h x hx
      by_cases hxv : x=v
      · subst x;exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (h (Finset.mem_erase.mpr ⟨hxv,hx⟩))
    · intro h x hx
      have hx' := Finset.mem_erase.mp hx
      exact (Finset.mem_insert.mp (h hx'.2)).resolve_left hx'.1
  simp only [inducedResourceWeight,hsub]
  split_ifs <;> rfl

theorem profile_root_weight_expectation [Fintype W]
    (e : (Σ i,V i) ↪ W) (R : C → Finset W) (w : C → ℝ) (v : W) (a m : I → ℕ)
    (hR : ∀ C₀,v∈R C₀ → w C₀≠0 → (R C₀).erase v⊆Finset.univ.map e)
    (ha : ∀ C₀,v∈R C₀ → w C₀≠0 → ∀ i,
      (Finset.univ.filter (fun u : V i => e ⟨i,u⟩∈(R C₀).erase v)).card=a i)
    [∀ i,Nonempty (FixedSubset (V i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (V i)) :
    (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))).expectation
      (fun σ => hypergraphWeightedDegree R (inducedResourceWeight R w (insert v ((profileRootSet σ).map e))) v)=
      (∏ i,((m i).choose (a i):ℝ)/(Fintype.card (V i)).choose (a i))*hypergraphWeightedDegree R w v := by
  simp only [induced_root_degree_sum]
  apply embedded_profile_weighted_support_expectation e (fun C₀ => (R C₀).erase v)
    (fun C₀ => if v∈R C₀ then w C₀ else 0) a m _ _ hm
  · intro C₀ h
    have hv : v∈R C₀ := by by_contra hh;simp [hh] at h
    have hw : w C₀≠0 := by simpa only [hv,ite_true] using h
    exact hR C₀ hv hw
  · intro C₀ h i
    have hv : v∈R C₀ := by by_contra hh;simp [hh] at h
    have hw : w C₀≠0 := by simpa only [hv,ite_true] using h
    exact ha C₀ hv hw i

theorem scaled_near_unit_product_error (p x η δ : ℝ) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hx : |x-1| ≤ η) (hp : |p-1| ≤ δ) :
    |p*x-1| ≤ η+(1+η)*δ := by
  have hxa : |x| ≤ 1+η := by
    have hh := abs_add_le (x-1) 1
    simp only [sub_add_cancel,abs_one] at hh
    linarith
  calc
    _ = |(p-1)*x+(x-1)| := by congr 1;ring
    _ ≤ |(p-1)*x|+|x-1| := abs_add_le _ _
    _ ≤ δ*(1+η)+η := by
      rw [abs_mul]
      exact add_le_add (mul_le_mul hp hxa (abs_nonneg _) hδ) hx
    _ = _ := by ring

end Oberwolfach
