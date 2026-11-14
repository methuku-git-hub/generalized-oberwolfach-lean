module

public import Oberwolfach.FixedSizeProfileConditioning
public import Oberwolfach.ProfileLinearRateConcentration
public import Oberwolfach.ConditionedProfileSampling

@[expose] public section

/-! Uniform conditional concentration for the normalized number of
actual labelled absorbers on the original sample space. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 256
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem normalized_count_exchange_coefficient (h : ℕ) (hh : 1 ≤ h)
    (K D t n : ℝ) (hK : 0 ≤ K) (ht : 0 < t) (hn0 : 0 ≤ n) (hn : n ≤ D*t) :
    (2*K*n^(h-1))/t^h ≤ (2*K*D^(h-1))/t := by
  calc
    _ ≤ (2*K*(D*t)^(h-1))/t^h := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn0 hn _) (by positivity)) (by positivity)
    _ = _ := by
      rw [mul_pow]
      have hp : t^h=t^(h-1)*t := by rw [← pow_succ];congr 1;omega
      rw [hp]
      field_simp

variable {s : ℕ} {V : Fin s → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
    {W C Tpl : Type*} [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]
    [Fintype Tpl] [DecidableEq Tpl] {c : ℕ}

theorem profile_fixed_size_absorber_linear_tail
    (e : (Σ i,V i) ↪ W) (R : C → Finset W) (S : Tpl → VertexAbsorberTemplate c)
    (hc : 1 ≤ c) (X : Finset W) (hX : X.card ≤ c) (J : ℕ)
    (hJ : ∀ Y : Finset W,Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (T : ∀ i,Finset (V i)) (m : Fin s → ℕ) (hT : ∀ i,(T i).card ≤ m i)
    [∀ i,Nonempty (FixedSubset {v : V i // v∉T i} (m i-(T i).card))]
    [∀ i,Nonempty (FixedSubset (V i) (m i))]
    (hm : ∀ i,m i-(T i).card ≤ Fintype.card {v : V i // v∉T i})
    (t ξ : ℝ) (ht : 1 ≤ t) (hξ : 0 ≤ ξ)
    (hsteps : ∑ i,((m i-(T i).card:ℕ):ℝ) ≤ c*t)
    (hroot : (Finset.univ.sigma T).map e⊆X) :
    let μ := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))
    let ν := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset {v : V i // v∉T i} (m i-(T i).card)))
    let f := fun τ => absorberGroundCount R S X ((profileRootSet τ).map e)/t^(c*c)
    let mean := ν.expectation (fun σ => f (fillProfileRootsAtSize T m hT σ))
    let K := ((c*c)*Fintype.card Tpl*c^c*J^(2*c+1):ℕ)
    let L := 1+2*(K:ℝ)*((c:ℝ)+1)^(c*c-1)
    μ.probability (fun τ => (∀ i,T i⊆(τ i).val) ∧ ξ ≤ |f τ-mean|) ≤
      μ.probability (fun τ => ∀ i,T i⊆(τ i).val)*
        (2*Real.exp (-(2*ξ^2/((c:ℝ)*L^2))*t)) := by
  let k := fun i => m i-(T i).card
  let e' := (profileRootFreeEmbedding T).trans e
  let K := ((c*c)*Fintype.card Tpl*c^c*J^(2*c+1):ℕ)
  let L := 1+2*(K:ℝ)*((c:ℝ)+1)^(c*c-1)
  let f := fun τ : ∀ i,FixedSubset (V i) (m i) => absorberGroundCount R S X ((profileRootSet τ).map e)/t^(c*c)
  let g := fun σ : ∀ i,FixedSubset {v : V i // v∉T i} (k i) => f (fillProfileRootsAtSize T m hT σ)
  have htpos : 0<t := by linarith
  have hcpos : (0:ℝ)<c := by exact_mod_cast (show 0<c by omega)
  have hh : 1≤c*c := by nlinarith
  have hL : 0<L := by dsimp [L];positivity
  have hg (σ : ∀ i,FixedSubset {v : V i // v∉T i} (k i)) :
      g σ=absorberGroundCount R S X ((profileRootSet σ).map e')/t^(c*c) := by
    dsimp [g,f]
    rw [fillProfileRootsAtSize_ground,Finset.map_union,Finset.map_map,
      absorberGroundCount_remove_fixed_roots R S X _ _ hroot]
  have hK : ((c*c)*Fintype.card Tpl*X.card^c*J^(2*c+1):ℕ) ≤ K := by
    dsimp [K]
    gcongr
  have hsize : ((∑ i,k i)+1:ℕ) ≤ ((c:ℝ)+1)*t := by
    have hsum : ((∑ i,k i:ℕ):ℝ) ≤ c*t := by simpa only [Nat.cast_sum] using hsteps
    push_cast
    nlinarith
  have hexchange : ∀ i σ τ,(∀ j,j≠i → σ j=τ j) → ∀ x y : {v : V i // v∉T i},
      τ i=fixedSubsetMap (Equiv.swap x y) (σ i) → |g σ-g τ| ≤ L/t := by
    intro i σ τ ha x y he
    rw [hg,hg,← sub_div,abs_div,abs_of_pos (pow_pos htpos _)]
    have hraw := absorber_profile_count_exchange e' R S X J hJ σ τ i ha x y
      (by convert he using 1 <;> congr!)
    have hraw' : |absorberGroundCount R S X ((profileRootSet σ).map e')-
        absorberGroundCount R S X ((profileRootSet τ).map e')| ≤
        2*(K:ℝ)*((∑ i,k i)+1:ℕ)^(c*c-1) := by
      apply (show |_ - _| ≤ _ by convert hraw using 1 <;> congr!).trans
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hK) (show (0:ℝ) ≤ 2 by norm_num)) (by positivity)
    apply (div_le_div_of_nonneg_right hraw' (by positivity)).trans
    apply (normalized_count_exchange_coefficient (c*c) hh K (c+1) t ((∑ i,k i)+1:ℕ)
      (by positivity) htpos (by positivity) hsize).trans
    apply div_le_div_of_nonneg_right _ htpos.le
    dsimp [L]
    linarith
  have htail := uniform_profile_linear_rate_tail k hm g c L t ξ hcpos hL htpos hξ hsteps
    (fun i σ τ ha x y he => hexchange i σ τ ha x y (by convert he using 1 <;> congr!))
  have hlaw := profile_fixed_size_conditional_probability T m hT
    (fun τ => ξ ≤ |f τ-(FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset {v : V i // v∉T i} (k i)))).expectation g|)
  dsimp only
  rw [hlaw]
  exact mul_le_mul_of_nonneg_left htail (finiteLaw_probability_nonneg _ _)

end Oberwolfach
