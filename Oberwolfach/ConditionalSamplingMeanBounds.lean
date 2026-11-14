module

public import Oberwolfach.ConditionedProfileRatios
public import Oberwolfach.ConditionalRootMean
public import Oberwolfach.ConditionalAbsorberMean
public import Oberwolfach.AbsorberDeletionMeanLower
public import Oberwolfach.UniformResourceWeights
public import Oberwolfach.AbsorberRestrictionScales

@[expose] public section

/-! Quantitative conditional means derived from the original host data.
The weights are fixed on the original identifiers. The deleted set includes
both the forbidden vertices and the explicitly conditioned root labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 256
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
    {C : Type*} [Fintype C]

theorem profile_omitted_size_sum (a : I → ℕ) (ha : ∀ i,1 ≤ a i)
    (c : ℕ) (hs : ∑ i,a i=c) (j : I) :
    ∑ i,(a i-if j=i then 1 else 0)=c-1 := by
  rw [← hs,Finset.sum_tsub_distrib]
  · simp
  · intro i _
    split_ifs <;> simp_all

theorem profile_ambient_size (a : I → ℕ) (c : ℕ) (hs : ∑ i,a i=c)
    (k : ℝ) (hn : ∀ i,(Fintype.card (V i):ℝ)=a i*k) :
    (Fintype.card (Σ i,V i):ℝ)=c*k := by
  rw [Fintype.card_sigma,Nat.cast_sum]
  simp_rw [hn]
  rw [← Finset.sum_mul,← Nat.cast_sum,hs]

theorem conditional_root_mean_bound
    (a : I → ℕ) (ha : ∀ i,1 ≤ a i) (c J : ℕ) (hc : 2 ≤ c) (hs : ∑ i,a i=c)
    (R : C → Finset (Σ i,V i)) (w : C → ℝ)
    (hR : ∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i)
    (hJ : ∀ Y : Finset (Σ i,V i),Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (k F₀ B η : ℝ) (hk : 0<k) (hB : 0≤B) (hη : 0≤η)
    (hn : ∀ i,(Fintype.card (V i):ℝ)=a i*k)
    (hw : ∀ C₀,0≤w C₀ ∧ w C₀≤B/k^(c-1))
    (herr : ∀ v,|1-hypergraphWeightedDegree R w v|≤η)
    (F : Finset (Σ i,V i)) (hF : (F.card:ℝ)≤F₀)
    (T : ∀ i,Finset (ProfileRemainingClass F i)) (P t : ℕ)
    (hT : ∀ i,(T i).card≤P) (ht : P+(c-1)≤t)
    (hlarge : 2*(c-1:ℕ)*(F₀+P+(c-1:ℕ))≤k)
    (hTm : ∀ i,(T i).card≤a i*t)
    [∀ i,Nonempty (FixedSubset {v : ProfileRemainingClass F i // v∉T i} (a i*t-(T i).card))]
    (hm : ∀ i,a i*t-(T i).card≤Fintype.card {v : ProfileRemainingClass F i // v∉T i})
    (v : Σ i,V i) (hroot : (Finset.univ.sigma T).map (profileComplementEmbedding F)⊆{v}) :
    let ν := FiniteLaw.pi (fun i => FiniteLaw.uniform
      (FixedSubset {v : ProfileRemainingClass F i // v∉T i} (a i*t-(T i).card)))
    let K := B*J*(c:ℝ)^(c-2)/k
    let δ := 2*(c-1:ℕ)*(((P:ℝ)+(c-1:ℕ))/t+(F₀+P+(c-1:ℕ))/k)
    |ν.expectation (fun σ => (k/(t:ℝ))^(c-1)*hypergraphWeightedDegree R
      (inducedResourceWeight R w (insert v ((profileRootSet (fillProfileRootsAtSize T (fun i => a i*t) hTm σ)).map
        (profileComplementEmbedding F)))) v)-1| ≤
      (η+F₀*K)+(1+η+F₀*K)*δ := by
  let K := B*J*(c:ℝ)^(c-2)/k
  let δ := 2*(c-1:ℕ)*(((P:ℝ)+(c-1:ℕ))/t+(F₀+P+(c-1:ℕ))/k)
  let Z := F∪(Finset.univ.sigma T).map (profileComplementEmbedding F)
  have hF₀ : 0≤F₀ := (Nat.cast_nonneg _).trans hF
  have hK : 0≤K := by dsimp [K];positivity
  have hδ : 0≤δ := by dsimp [δ];positivity
  have hZ : Z.erase v⊆F := by
    intro x hx
    obtain ⟨hxv,hx⟩ := Finset.mem_erase.mp hx
    rcases Finset.mem_union.mp hx with hx|hx
    · exact hx
    · exact False.elim (hxv (Finset.mem_singleton.mp (hroot hx)))
  have hZcard : ((Z.erase v).card:ℝ)≤F₀ :=
    (by exact_mod_cast Finset.card_le_card hZ : ((Z.erase v).card:ℝ)≤F.card).trans hF
  have hRC (C₀ : C) : (R C₀).card=c := by rw [sigma_finset_card];simp_rw [hR];exact hs
  have hpair := uniform_resource_pair_weight R c J hc hRC hJ w B k hB hk
    (profile_ambient_size a c hs k hn) (fun C₀ => (hw C₀).2)
  have hload := resource_vertex_deletion_load_error R w (fun C₀ => (hw C₀).1) K η hK hpair herr
    (Z.erase v) v (Finset.notMem_erase _ _)
  have hload' : |hypergraphWeightedDegree R (vertexRestrictedWeight R w (Z.erase v)) v-1|≤η+F₀*K := by
    rw [abs_sub_comm] at hload
    exact hload.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hZcard hK))
  have hratio := conditioned_profile_inclusion_ratio a ha k F₀ hk hn F hF T P t hT
    (fun i => a i-if v.1=i then 1 else 0) (c-1) (profile_omitted_size_sum a ha c hs v.1)
    (by omega) ht hlarge
  have hmean := conditional_root_original_mean R w a hR F T (fun i => a i*t) hTm hm v hroot
  dsimp only
  rw [finiteLaw_expectation_const_mul,hmean]
  have hh := scaled_near_unit_product_error _ _ (η+F₀*K) δ (by positivity) hδ hload' hratio
  simpa only [K,δ,Z,mul_assoc,add_assoc] using hh

variable {Tpl : Type*} [Fintype Tpl] [DecidableEq Tpl] [DecidableEq C]

theorem conditional_absorber_mean_lower_from_host
    (a : I → ℕ) (ha : ∀ i,1 ≤ a i) (c J : ℕ) (hc : 1 ≤ c) (hs : ∑ i,a i=c)
    (R : C → Finset (Σ i,V i)) (S : Tpl → VertexAbsorberTemplate c)
    (hR : ∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i)
    (hJ : ∀ Y : Finset (Σ i,V i),Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (k F₀ α : ℝ) (hk : 0<k) (hα : 0≤α)
    (hn : ∀ i,(Fintype.card (V i):ℝ)=a i*k)
    (F X : Finset (Σ i,V i)) (hF : (F.card:ℝ)≤F₀) (hX : X.card=c)
    (hcount : α*k^(c*c) ≤ Fintype.card (LabelledAbsorberFamily R S X))
    (T : ∀ i,Finset (ProfileRemainingClass F i)) (t : ℕ)
    (hT : ∀ i,(T i).card≤c) (ht : c+c*c≤t)
    (hlarge : 2*(c*c:ℕ)*(F₀+c+(c*c:ℕ))≤k)
    (hTm : ∀ i,(T i).card≤a i*t)
    [∀ i,Nonempty (FixedSubset {v : ProfileRemainingClass F i // v∉T i} (a i*t-(T i).card))]
    (hm : ∀ i,a i*t-(T i).card≤Fintype.card {v : ProfileRemainingClass F i // v∉T i})
    (hroot : (Finset.univ.sigma T).map (profileComplementEmbedding F)⊆X)
    (hratio : 2*(c*c:ℕ)*(((c:ℝ)+(c*c:ℕ))/t+(F₀+c+(c*c:ℕ))/k)≤1/4)
    (hloss : 4*(F₀+c)*absorberVertexDeletionCoefficient c J (Fintype.card Tpl)≤α*k) :
    let ν := FiniteLaw.pi (fun i => FiniteLaw.uniform
      (FixedSubset {v : ProfileRemainingClass F i // v∉T i} (a i*t-(T i).card)))
    (α/2)*(t:ℝ)^(c*c) ≤ ν.expectation (fun σ => absorberGroundCount R S X
      ((profileRootSet (fillProfileRootsAtSize T (fun i => a i*t) hTm σ)).map (profileComplementEmbedding F))) := by
  let Z := F∪(Finset.univ.sigma T).map (profileComplementEmbedding F)
  let D := absorberVertexDeletionCoefficient c J (Fintype.card Tpl)
  have hD : 0≤D := by dsimp [D,absorberVertexDeletionCoefficient];positivity
  have hF₀ : 0≤F₀ := (Nat.cast_nonneg _).trans hF
  have hh : 1≤c*c := by nlinarith
  have htpos : (0:ℝ)<t := by exact_mod_cast (show 0<t by omega)
  have hZcard : (Z.card:ℝ)≤F₀+c := by
    have hcN := (Finset.card_le_card hroot).trans_eq hX
    have hu := Finset.card_union_le F ((Finset.univ.sigma T).map (profileComplementEmbedding F))
    have huR : (Z.card:ℝ)≤(F.card:ℝ)+((Finset.univ.sigma T).map (profileComplementEmbedding F)).card := by exact_mod_cast hu
    have hcR : (((Finset.univ.sigma T).map (profileComplementEmbedding F)).card:ℝ)≤c := by exact_mod_cast hcN
    linarith
  have hraw : (Z.card*((c*c)*Fintype.card Tpl*X.card^c*Fintype.card (Σ i,V i)^(c*c-1)*J^(2*c+1)):ℕ) =
      (Z.card:ℝ)*D*k^(c*c-1) := by
    push_cast
    rw [hX,profile_ambient_size a c hs k hn,mul_pow]
    dsimp [D,absorberVertexDeletionCoefficient]
    push_cast
    ring
  have hpow : k*k^(c*c-1)=k^(c*c) := by rw [← pow_succ'];congr 1;omega
  have hdel : (Z.card*((c*c)*Fintype.card Tpl*X.card^c*Fintype.card (Σ i,V i)^(c*c-1)*J^(2*c+1)):ℕ)≤α/4*k^(c*c) := by
    rw [hraw]
    calc
      _ ≤ (F₀+c)*D*k^(c*c-1) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hZcard hD) (by positivity)
      _ ≤ (α/4*k)*k^(c*c-1) := mul_le_mul_of_nonneg_right (by dsimp [D];nlinarith [hloss]) (by positivity)
      _ = _ := by rw [mul_assoc,hpow]
  let p := ∏ i,((a i*t-(T i).card).choose (c*a i):ℝ)/
      (Fintype.card {v : ProfileRemainingClass F i // v∉T i}).choose (c*a i)
  have hp : 0≤p := Finset.prod_nonneg (fun i _ => by positivity)
  have hrat : |(k/(t:ℝ))^(c*c)*p-1|≤1/4 :=
    (conditioned_profile_inclusion_ratio a ha k F₀ hk hn F hF T c t hT (fun i => c*a i) (c*c)
      (by rw [← Finset.mul_sum,hs]) hh ht hlarge).trans hratio
  have hgood := labelled_absorber_avoiding_lower R S X Z J hJ (α*k^(c*c)) (α/4*k^(c*c)) hcount hdel
  have hgood' : (3/4)*α*k^(c*c) ≤ (Fintype.card {D₀ : LabelledAbsorberFamily R S X //
      Disjoint (labelledAbsorberFree R (S D₀.1) X D₀.2) Z}:ℝ) := by linarith
  have hprob := sampling_probability_scaled_lower p k t (1/4) (c*c) htpos hrat
  dsimp only
  rw [conditional_absorber_original_mean R S a hR F X T (fun i => a i*t) hTm hm hroot]
  change _ ≤ p*_
  calc
    _ ≤ (3/4)*α*((1-1/4)*(t:ℝ)^(c*c)) := by nlinarith [pow_nonneg htpos.le (c*c)]
    _ ≤ (3/4)*α*(p*k^(c*c)) := mul_le_mul_of_nonneg_left hprob (by positivity)
    _ = p*((3/4)*α*k^(c*c)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hgood' hp

end Oberwolfach
