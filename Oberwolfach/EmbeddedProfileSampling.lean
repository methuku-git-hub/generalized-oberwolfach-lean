module

public import Oberwolfach.ProfileSamplingProbabilities
public import Oberwolfach.InducedResourceWeights

@[expose] public section

/-! Exact expectations after retaining fixed vertices and uniformly
sampling the remaining populations. The embedding into the ambient
vertex set is explicit, including when the root is outside a population. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
    {W : Type*} [DecidableEq W]

def profileFreePreimage (e : (Σ i,V i) ↪ W) (Z A : Finset W) : Finset (Σ i,V i) :=
  Finset.univ.filter (fun x => e x∈A ∧ e x∉Z)

theorem embedded_profile_subset_iff (e : (Σ i,V i) ↪ W) (Z A : Finset W)
    (hA : A⊆Z∪Finset.univ.map e) {m : I → ℕ} (σ : ∀ i,FixedSubset (V i) (m i)) :
    A⊆Z∪(profileRootSet σ).map e ↔ profileFreePreimage e Z A⊆profileRootSet σ := by
  constructor
  · intro h x hx
    have hx' := (Finset.mem_filter.mp hx).2
    have hm := (Finset.mem_union.mp (h hx'.1)).resolve_left hx'.2
    obtain ⟨y,hy,he⟩ := Finset.mem_map.mp hm
    have he' := e.injective he
    subst y
    exact hy
  · intro h x hx
    by_cases hz : x∈Z
    · exact Finset.mem_union_left _ hz
    · obtain ⟨y,_,rfl⟩ := Finset.mem_map.mp ((Finset.mem_union.mp (hA hx)).resolve_left hz)
      exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨y,
        h (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx,hz⟩),rfl⟩)

theorem embedded_profile_inclusion_probability (e : (Σ i,V i) ↪ W) (Z A : Finset W)
    (hA : A⊆Z∪Finset.univ.map e) (m : I → ℕ)
    [∀ i,Nonempty (FixedSubset (V i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (V i)) :
    (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))).probability
      (fun σ => A⊆Z∪(profileRootSet σ).map e)=
    ∏ i,((m i).choose (Finset.univ.filter (fun v : V i => e ⟨i,v⟩∈A ∧ e ⟨i,v⟩∉Z)).card:ℝ)/
      (Fintype.card (V i)).choose (Finset.univ.filter (fun v : V i => e ⟨i,v⟩∈A ∧ e ⟨i,v⟩∉Z)).card := by
  have hp : (fun σ : ∀ i,FixedSubset (V i) (m i) => A⊆Z∪(profileRootSet σ).map e)=
      (fun σ => profileFreePreimage e Z A⊆profileRootSet σ) :=
    funext (fun σ => propext (embedded_profile_subset_iff e Z A hA σ))
  rw [hp,profile_subset_inclusion_probability m hm]
  simp only [profileFreePreimage,Finset.mem_filter,Finset.mem_univ,true_and]

theorem embedded_profile_weighted_degree_expectation [Fintype W]
    {C : Type*} [Fintype C] (e : (Σ i,V i) ↪ W) (Z : Finset W)
    (R : C → Finset W) (w : C → ℝ) (v : W)
    (hR : ∀ C₀,v∈R C₀ → R C₀⊆Z∪Finset.univ.map e) (m : I → ℕ)
    [∀ i,Nonempty (FixedSubset (V i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (V i)) :
    (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))).expectation
      (fun σ => hypergraphWeightedDegree R (inducedResourceWeight R w (Z∪(profileRootSet σ).map e)) v)=
    ∑ C₀,if v∈R C₀ then w C₀*
      ∏ i,((m i).choose (Finset.univ.filter (fun u : V i => e ⟨i,u⟩∈R C₀ ∧ e ⟨i,u⟩∉Z)).card:ℝ)/
        (Fintype.card (V i)).choose (Finset.univ.filter (fun u : V i => e ⟨i,u⟩∈R C₀ ∧ e ⟨i,u⟩∉Z)).card
      else 0 := by
  simp only [hypergraphWeightedDegree]
  rw [finiteLaw_expectation_sum]
  apply Finset.sum_congr rfl
  intro C₀ _
  by_cases hv : v∈R C₀
  · simp only [hv,ite_true,inducedResourceWeight]
    rw [finiteLaw_expectation_indicator_value,embedded_profile_inclusion_probability e Z (R C₀) (hR C₀ hv) m hm]
  · simp only [hv,ite_false,finiteLaw_expectation_const]

end Oberwolfach
