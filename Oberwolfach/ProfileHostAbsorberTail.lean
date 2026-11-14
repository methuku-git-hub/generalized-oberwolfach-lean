module

public import Oberwolfach.ConditionalSamplingMeanBounds
public import Oberwolfach.ProfileSampleEligibility
public import Oberwolfach.FixedSizeAbsorberSampling

@[expose] public section

/-! An eligible root's absorber count is large with a conditional
probability bound derived from the original host abundance. All
labelled absorber identifiers and the original sample law are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 256
set_option maxHeartbeats 4400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {V : Fin s → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
    {C Tpl : Type*} [Fintype C] [DecidableEq C] [Fintype Tpl] [DecidableEq Tpl]

theorem profile_host_absorber_tail
    (a : Fin s → ℕ) (ha : ∀ i,1≤a i) (c J : ℕ) (hc : 1≤c) (hs : ∑ i,a i=c)
    (R : C → Finset (Σ i,V i)) (S : Tpl → VertexAbsorberTemplate c)
    (hR : ∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i)
    (hJ : ∀ Y : Finset (Σ i,V i),Fintype.card {C₀ : C // R C₀=Y}≤J)
    (k F₀ α : ℝ) (hk : 0<k) (hα : 0≤α)
    (hn : ∀ i,(Fintype.card (V i):ℝ)=a i*k)
    (F Z X : Finset (Σ i,V i)) (hF : (F.card:ℝ)≤F₀) (hX : X.card=c)
    (hcount : α*k^(c*c)≤Fintype.card (LabelledAbsorberFamily R S X))
    (t : ℕ) (ht : c+c*c≤t)
    [∀ i,Nonempty (FixedSubset (ProfileRemainingClass F i) (a i*t))]
    (hm : ∀ i,a i*t≤Fintype.card (ProfileRemainingClass F i))
    (hlarge : 2*(c*c:ℕ)*(F₀+c+(c*c:ℕ))≤k)
    (hratio : 2*(c*c:ℕ)*(((c:ℝ)+(c*c:ℕ))/t+(F₀+c+(c*c:ℕ))/k)≤1/4)
    (hloss : 4*(F₀+c)*absorberVertexDeletionCoefficient c J (Fintype.card Tpl)≤α*k) :
    let μ := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (ProfileRemainingClass F i) (a i*t)))
    let K := ((c*c)*Fintype.card Tpl*c^c*J^(2*c+1):ℕ)
    let L := 1+2*(K:ℝ)*((c:ℝ)+1)^(c*c-1)
    μ.probability (fun τ => X⊆(profileRootSet τ).map (profileComplementEmbedding F)∪Z ∧
      absorberGroundCount R S X ((profileRootSet τ).map (profileComplementEmbedding F))<(α/4)*(t:ℝ)^(c*c))≤
      (2*Real.exp (-(2*(α/4)^2/((c:ℝ)*L^2))*(t:ℝ)))*
        μ.probability (fun τ => X⊆(profileRootSet τ).map (profileComplementEmbedding F)∪Z) := by
  let μ := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (ProfileRemainingClass F i) (a i*t)))
  let f := fun τ : ∀ i,FixedSubset (ProfileRemainingClass F i) (a i*t) =>
    absorberGroundCount R S X ((profileRootSet τ).map (profileComplementEmbedding F))/(t:ℝ)^(c*c)
  let K := ((c*c)*Fintype.card Tpl*c^c*J^(2*c+1):ℕ)
  let L := 1+2*(K:ℝ)*((c:ℝ)+1)^(c*c-1)
  let Y := fun τ : ∀ i,FixedSubset (ProfileRemainingClass F i) (a i*t) =>
    (profileRootSet τ).map (profileComplementEmbedding F)∪Z
  change μ.probability (fun τ => X⊆Y τ ∧ _)<=(2*Real.exp _)*μ.probability (fun τ => X⊆Y τ)
  by_cases hcompat : X∩F⊆Z
  · let T := profileRequiredRoots F Z X
    have hT (i) : (T i).card≤c := (profileRequiredRoots_card F Z X i).trans_eq hX
    obtain ⟨hTm,hm'⟩ := profile_conditioned_sample_feasible a ha c t (by omega) F T hT hm
    letI : ∀ i,Nonempty (FixedSubset {u : ProfileRemainingClass F i // u∉T i} (a i*t-(T i).card)) := fun i => fixedSubset_nonempty (hm' i)
    let ν := FiniteLaw.pi (fun i => FiniteLaw.uniform
      (FixedSubset {u : ProfileRemainingClass F i // u∉T i} (a i*t-(T i).card)))
    let mean := ν.expectation (fun σ => f (fillProfileRootsAtSize T (fun i => a i*t) hTm σ))
    have helig (τ : ∀ i,FixedSubset (ProfileRemainingClass F i) (a i*t)) :
        X⊆Y τ ↔ ∀ i,T i⊆(τ i).val :=
      profileRequiredRoots_eligibility F Z X hcompat (fun i => a i*t) τ
    have hroot := profileRequiredRoots_map_subset F Z X
    have htR : (1:ℝ)≤t := by exact_mod_cast (show 1≤t by omega)
    have htpos : (0:ℝ)<t := by linarith
    have hmean : α/2≤mean := by
      have hh := conditional_absorber_mean_lower_from_host a ha c J hc hs R S hR hJ k F₀ α hk hα hn
        F X hF hX hcount T t hT ht hlarge hTm hm' hroot hratio hloss
      have hid : mean=ν.expectation (fun σ => absorberGroundCount R S X
          ((profileRootSet (fillProfileRootsAtSize T (fun i => a i*t) hTm σ)).map (profileComplementEmbedding F)))/(t:ℝ)^(c*c) := by
        simp only [mean,f,FiniteLaw.expectation,mul_div_assoc,Finset.sum_div]
      rw [hid]
      exact (le_div_iff₀ (pow_pos htpos _)).mpr hh
    have htail := profile_fixed_size_absorber_linear_tail (profileComplementEmbedding F) R S hc X hX.le J hJ
      T (fun i => a i*t) hTm hm' t (α/4) htR (by positivity) (profile_conditioned_sample_steps a c t hs F T) hroot
    have htail' : μ.probability (fun τ => (∀ i,T i⊆(τ i).val) ∧ α/4≤|f τ-mean|)≤
        μ.probability (fun τ => ∀ i,T i⊆(τ i).val)*(2*Real.exp (-(2*(α/4)^2/((c:ℝ)*L^2))*(t:ℝ))) := htail
    apply (finiteLaw_probability_mono μ _ _ ?_).trans htail' |>.trans_eq ?_
    · intro τ hτ
      refine ⟨(helig τ).mp hτ.1,?_⟩
      have hf : f τ<α/4 := (div_lt_iff₀ (pow_pos htpos _)).mpr hτ.2
      have hh := neg_le_abs (f τ-mean)
      linarith
    · rw [mul_comm]
      congr 1
      apply congrArg μ.probability
      funext τ
      exact propext (helig τ).symm
  · have hnone (τ : ∀ i,FixedSubset (ProfileRemainingClass F i) (a i*t)) : ¬X⊆Y τ := by
      intro hXτ
      exact hcompat (profile_eligible_root_compatible F Z X (fun i => a i*t) τ hXτ)
    simp only [Y] at hnone
    simp only [FiniteLaw.probability,Y,hnone,false_and,ite_false,Finset.sum_const_zero,mul_zero,le_refl]

end Oberwolfach
