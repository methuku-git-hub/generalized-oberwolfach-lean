module

public import Oberwolfach.ProfileSeparationSampling
public import Oberwolfach.ProfileRemainingSampleMargins
public import Oberwolfach.DisjointSingletonSampling

@[expose] public section

/-! The forbidden pairs are given on the original ambient vertices.
All probabilities are taken on the actual smaller class populations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]

theorem embedded_profile_pair_probability {W : Type*} [DecidableEq W]
    (e : (Σ i,V i) ↪ W) (m : I → ℕ)
    [∀ i,Nonempty (FixedSubset (V i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (V i)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hρm : ∀ i,(m i:ℝ)/Fintype.card (V i) ≤ ρ) (x y : W) (hxy : x≠y) :
    (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))).probability
      (fun σ => x∈(profileRootSet σ).map e ∧ y∈(profileRootSet σ).map e) ≤ ρ^2 := by
  by_cases hx : ∃ u,e u=x
  · obtain ⟨u,rfl⟩ := hx
    by_cases hy : ∃ v,e v=y
    · obtain ⟨v,rfl⟩ := hy
      simpa only [Finset.mem_map,e.injective.eq_iff,exists_eq_right] using
        profile_pair_inclusion_upper m hm ρ hρ hρm u v (fun he => hxy (congrArg e he))
    · have hp : (fun σ : ∀ i,FixedSubset (V i) (m i) =>
          e u∈(profileRootSet σ).map e ∧ y∈(profileRootSet σ).map e)=fun _ => False := by
        funext σ
        apply propext
        simp only [iff_false]
        intro hh
        obtain ⟨v,_,he⟩ := Finset.mem_map.mp hh.2
        exact hy ⟨v,he⟩
      rw [hp,finiteLaw_probability_false]
      positivity
  · have hp : (fun σ : ∀ i,FixedSubset (V i) (m i) =>
        x∈(profileRootSet σ).map e ∧ y∈(profileRootSet σ).map e)=fun _ => False := by
      funext σ
      apply propext
      simp only [iff_false]
      intro hh
      obtain ⟨v,_,he⟩ := Finset.mem_map.mp hh.1
      exact hx ⟨v,he⟩
    rw [hp,finiteLaw_probability_false]
    positivity

theorem embedded_profile_forbidden_pairs_probability {W : Type*} [DecidableEq W]
    (e : (Σ i,V i) ↪ W) (m : I → ℕ)
    [∀ i,Nonempty (FixedSubset (V i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (V i)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hρm : ∀ i,(m i:ℝ)/Fintype.card (V i) ≤ ρ)
    (E : Finset (W×W)) (hE : ∀ e∈E,e.1≠e.2) :
    (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))).probability
      (fun σ => ∃ f∈E,f.1∈(profileRootSet σ).map e ∧ f.2∈(profileRootSet σ).map e) ≤
      (E.card:ℝ)*ρ^2 := by
  apply (finiteLaw_union_bound _ E (fun f σ => f.1∈(profileRootSet σ).map e ∧ f.2∈(profileRootSet σ).map e)).trans
  calc
    _ ≤ ∑ _f∈E,ρ^2 := Finset.sum_le_sum (fun f hf => embedded_profile_pair_probability e m hm ρ hρ hρm f.1 f.2 (hE f hf))
    _ = _ := by simp

theorem profile_remaining_forbidden_pairs_probability
    (a : I → ℕ) (ha : ∀ i,1 ≤ a i) (k F t D : ℝ)
    (hk : 0 < k) (ht : 0 ≤ t) (hF : 2*F ≤ k)
    (hn : ∀ i,(Fintype.card (V i):ℝ)=a i*k) (Z : Finset (Σ i,V i))
    (hZ : (Z.card:ℝ) ≤ F) (m : I → ℕ)
    [∀ i,Nonempty (FixedSubset (ProfileRemainingClass Z i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (ProfileRemainingClass Z i))
    (hmt : ∀ i,(m i:ℝ) ≤ a i*t)
    (E : Finset ((Σ i,V i)×(Σ i,V i))) (hE : ∀ e∈E,e.1≠e.2)
    (hsize : (E.card:ℝ) ≤ D*k) :
    (FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (ProfileRemainingClass Z i) (m i)))).probability
      (fun σ => ∃ f∈E,f.1∈(profileRootSet σ).map (profileComplementEmbedding Z) ∧
        f.2∈(profileRootSet σ).map (profileComplementEmbedding Z)) ≤ 4*D*t^2/k := by
  have hh := embedded_profile_forbidden_pairs_probability (profileComplementEmbedding Z) m hm (2*t/k)
    (by positivity) (profile_remaining_sampling_ratio a ha k F t hk ht hF hn Z hZ m hmt) E hE
  apply hh.trans
  calc
    _ ≤ (D*k)*(2*t/k)^2 := mul_le_mul_of_nonneg_right hsize (sq_nonneg _)
    _ = _ := by field_simp;ring

end Oberwolfach
