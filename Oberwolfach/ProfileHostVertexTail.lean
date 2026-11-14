module

public import Oberwolfach.ConditionalSamplingMeanBounds
public import Oberwolfach.ProfileSampleEligibility
public import Oberwolfach.FixedSizeWeightedSampling

@[expose] public section

/-! Vertex tests on a fixed-size sample, with the conditional mean
estimated from the original host weights, including external vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 256
set_option maxHeartbeats 4200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem induced_degree_scale {W C : Type*} [DecidableEq W] [Fintype C]
    (R : C → Finset W) (w : C → ℝ) (p : ℝ) (A : Finset W) (v : W) :
    hypergraphWeightedDegree R (inducedResourceWeight R (fun C₀ => p*w C₀) A) v=
      p*hypergraphWeightedDegree R (inducedResourceWeight R w A) v := by
  simp only [hypergraphWeightedDegree,inducedResourceWeight,Finset.mul_sum,mul_ite,mul_zero]

theorem rescaled_individual_weight (d : ℕ) (k t B w : ℝ) (hk : 0<k) (ht : 0<t)
    (hw : 0≤w ∧ w≤B/k^d) : 0≤(k/t)^d*w ∧ (k/t)^d*w≤B/t^d := by
  constructor
  · exact mul_nonneg (by positivity) hw.1
  · calc
      _ ≤ (k/t)^d*(B/k^d) := mul_le_mul_of_nonneg_left hw.2 (by positivity)
      _ = _ := by rw [div_pow];field_simp

variable {s : ℕ} {V : Fin s → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
    {C : Type*} [Fintype C]

theorem profile_host_vertex_tail
    (a : Fin s → ℕ) (ha : ∀ i,1≤a i) (c J : ℕ) (hc : 2≤c) (hJpos : 1≤J) (hs : ∑ i,a i=c)
    (R : C → Finset (Σ i,V i)) (w : C → ℝ)
    (hR : ∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i)
    (hJ : ∀ Y : Finset (Σ i,V i),Fintype.card {C₀ : C // R C₀=Y}≤J)
    (k F₀ B η ξ : ℝ) (hk : 0<k) (hB : 0<B) (hη : 0≤η) (hξ : 0≤ξ)
    (hn : ∀ i,(Fintype.card (V i):ℝ)=a i*k)
    (hw : ∀ C₀,0≤w C₀ ∧ w C₀≤B/k^(c-1))
    (herr : ∀ v,|1-hypergraphWeightedDegree R w v|≤η)
    (F Z : Finset (Σ i,V i)) (hF : (F.card:ℝ)≤F₀) (t : ℕ) (ht : c≤t)
    [∀ i,Nonempty (FixedSubset (ProfileRemainingClass F i) (a i*t))]
    (hm : ∀ i,a i*t≤Fintype.card (ProfileRemainingClass F i))
    (hlarge : 2*(c-1:ℕ)*(F₀+1+(c-1:ℕ))≤k)
    (hmargin :
      (η+F₀*(B*J*(c:ℝ)^(c-2)/k))+
      (1+η+F₀*(B*J*(c:ℝ)^(c-2)/k))*
        (2*(c-1:ℕ)*(((1:ℝ)+(c-1:ℕ))/t+(F₀+1+(c-1:ℕ))/k))≤ξ)
    (v : Σ i,V i) :
    let μ := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (ProfileRemainingClass F i) (a i*t)))
    let wt := fun C₀ => (k/(t:ℝ))^(c-1)*w C₀
    let f := fun τ => hypergraphWeightedDegree R (inducedResourceWeight R wt
      (insert v ((profileRootSet τ).map (profileComplementEmbedding F)))) v
    let L := 2*(J:ℝ)*(2*(c:ℝ)+1)^(c-2)*B
    μ.probability (fun τ => v∈(profileRootSet τ).map (profileComplementEmbedding F)∪Z ∧ 2*ξ< |1-f τ|)≤
      (2*Real.exp (-(2*ξ^2/((c:ℝ)*L^2))*(t:ℝ)))*
        μ.probability (fun τ => v∈(profileRootSet τ).map (profileComplementEmbedding F)∪Z) := by
  let μ := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (ProfileRemainingClass F i) (a i*t)))
  let wt := fun C₀ => (k/(t:ℝ))^(c-1)*w C₀
  let f := fun τ : ∀ i,FixedSubset (ProfileRemainingClass F i) (a i*t) =>
    hypergraphWeightedDegree R (inducedResourceWeight R wt (insert v ((profileRootSet τ).map (profileComplementEmbedding F)))) v
  let L := 2*(J:ℝ)*(2*(c:ℝ)+1)^(c-2)*B
  let Y := fun τ : ∀ i,FixedSubset (ProfileRemainingClass F i) (a i*t) =>
    (profileRootSet τ).map (profileComplementEmbedding F)∪Z
  change μ.probability (fun τ => v∈Y τ ∧ 2*ξ< |1-f τ|)≤_
  by_cases hcompat : {v}∩F⊆Z
  · let T := profileRequiredRoots F Z {v}
    have hT (i) : (T i).card≤1 := by simpa only [Finset.card_singleton] using profileRequiredRoots_card F Z {v} i
    obtain ⟨hTm,hm'⟩ := profile_conditioned_sample_feasible a ha 1 t (by omega) F T hT hm
    letI : ∀ i,Nonempty (FixedSubset {u : ProfileRemainingClass F i // u∉T i} (a i*t-(T i).card)) := fun i => fixedSubset_nonempty (hm' i)
    let ν := FiniteLaw.pi (fun i => FiniteLaw.uniform
      (FixedSubset {u : ProfileRemainingClass F i // u∉T i} (a i*t-(T i).card)))
    let mean := ν.expectation (fun σ => f (fillProfileRootsAtSize T (fun i => a i*t) hTm σ))
    have helig (τ : ∀ i,FixedSubset (ProfileRemainingClass F i) (a i*t)) :
        v∈Y τ ↔ ∀ i,T i⊆(τ i).val := by
      simpa only [Finset.singleton_subset_iff] using profileRequiredRoots_eligibility F Z {v} hcompat (fun i => a i*t) τ
    have hroot := profileRequiredRoots_map_subset F Z {v}
    have hmean : |mean-1|≤ξ := by
      have hh := conditional_root_mean_bound a ha c J hc hs R w hR hJ k F₀ B η hk hB.le hη hn hw herr F hF T 1 t hT
        (by omega) (by simpa only [Nat.cast_one] using hlarge) hTm hm' v hroot
      have hid : mean=ν.expectation (fun σ => (k/(t:ℝ))^(c-1)*hypergraphWeightedDegree R
          (inducedResourceWeight R w (insert v ((profileRootSet (fillProfileRootsAtSize T (fun i => a i*t) hTm σ)).map
            (profileComplementEmbedding F)))) v) := by
        dsimp [mean,f,wt]
        simp_rw [induced_degree_scale]
      rw [hid]
      exact hh.trans (by simpa only [Nat.cast_one] using hmargin)
    have htR : (1:ℝ)≤t := by exact_mod_cast (show 1≤t by omega)
    have htpos : (0:ℝ)<t := by linarith
    have hRC (C₀ : C) : (R C₀).card=c := by rw [sigma_finset_card];simp_rw [hR];exact hs
    have hroots : ({v}∪(Finset.univ.sigma T).map (profileComplementEmbedding F)).card≤c := by
      rw [Finset.union_eq_left.mpr hroot,Finset.card_singleton]
      omega
    have htail := profile_fixed_size_weighted_linear_tail (profileComplementEmbedding F) R c J hc hJpos hRC hJ wt B t ξ
      hB htR hξ (fun C₀ => rescaled_individual_weight (c-1) k t B (w C₀) hk htpos (hw C₀))
      {v} T (fun i => a i*t) hTm hm' (profile_conditioned_sample_steps a c t hs F T) hroots v
      (Finset.mem_union_left _ (Finset.mem_singleton_self _))
    have htail' : μ.probability (fun τ => (∀ i,T i⊆(τ i).val) ∧ ξ≤|f τ-mean|)≤
        μ.probability (fun τ => ∀ i,T i⊆(τ i).val)*(2*Real.exp (-(2*ξ^2/((c:ℝ)*L^2))*(t:ℝ))) := by
      simpa only [Finset.singleton_union] using htail
    apply (finiteLaw_probability_mono μ _ _ ?_).trans htail' |>.trans_eq ?_
    · intro τ hτ
      refine ⟨(helig τ).mp hτ.1,?_⟩
      have htri := abs_sub_le (1:ℝ) mean (f τ)
      rw [abs_sub_comm 1 mean,abs_sub_comm mean (f τ)] at htri
      linarith [hτ.2]
    · rw [mul_comm]
      congr 1
      apply congrArg μ.probability
      funext τ
      exact propext (helig τ).symm
  · have hnone (τ : ∀ i,FixedSubset (ProfileRemainingClass F i) (a i*t)) : v∉Y τ := by
      intro hv
      apply hcompat
      exact profile_eligible_root_compatible F Z {v} (fun i => a i*t) τ (Finset.singleton_subset_iff.mpr hv)
    simp only [Y] at hnone
    simp only [FiniteLaw.probability,Y,hnone,false_and,ite_false,Finset.sum_const_zero,mul_zero,le_refl]

end Oberwolfach
