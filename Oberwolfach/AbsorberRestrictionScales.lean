module

public import Oberwolfach.AbsorberRestrictionLoss

@[expose] public section

/-! Explicit deletion and scale substitutions for the labelled
absorber abundance and the supplied individual resource weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 2800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W C T : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    [Fintype C] [DecidableEq C] [Fintype T] [DecidableEq T] {c : ℕ}

def absorberVertexDeletionCoefficient (c J N : ℕ) : ℝ :=
  (c*c:ℕ)*N*(c:ℝ)^c*(c:ℝ)^(c*c-1)*(J:ℝ)^(2*c+1)

theorem restricted_absorber_card_loss_scale (R : C → Finset V) (e : W ↪ V)
    (S : T → VertexAbsorberTemplate c) (X : Finset W) (Z : Finset V)
    (he : ∀ v,(∃ w,e w=v) ↔ v∉Z) (J : ℕ)
    (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (k : ℝ) (hn : (Fintype.card V:ℝ)=c*k) (hX : X.card=c) :
    (Fintype.card (LabelledAbsorberFamily R S (X.image e)):ℝ) ≤
      Fintype.card (LabelledAbsorberFamily (restrictedResourceSet R e) S X)+
      Z.card*absorberVertexDeletionCoefficient c J (Fintype.card T)*k^(c*c-1) := by
  have hh := restricted_absorber_card_loss R e S X Z he J hJ
  rw [hX] at hh
  have hhR : (Fintype.card (LabelledAbsorberFamily R S (X.image e)):ℝ) ≤
      Fintype.card (LabelledAbsorberFamily (restrictedResourceSet R e) S X)+
      Z.card*((c*c:ℕ)*(Fintype.card T:ℝ)*(c:ℝ)^c*(Fintype.card V:ℝ)^(c*c-1)*(J:ℝ)^(2*c+1)) := by
    exact_mod_cast hh
  rw [hn,mul_pow] at hhR
  convert hhR using 1 <;> dsimp [absorberVertexDeletionCoefficient] <;> ring

theorem restricted_absorber_abundance (hc : 1 ≤ c)
    (R : C → Finset V) (e : W ↪ V)
    (S : T → VertexAbsorberTemplate c) (X : Finset W) (Z : Finset V)
    (he : ∀ v,(∃ w,e w=v) ↔ v∉Z) (J : ℕ)
    (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (k k' a δ : ℝ) (hk : 0 < k) (hk' : 0 ≤ k') (hkk' : k' ≤ k) (ha : 0 ≤ a)
    (hn : (Fintype.card V:ℝ)=c*k) (hX : X.card=c)
    (hZ : (Z.card:ℝ) ≤ δ*k)
    (hsmall : δ*absorberVertexDeletionCoefficient c J (Fintype.card T) ≤ a/2)
    (habs : a*k^(c*c) ≤ Fintype.card (LabelledAbsorberFamily R S (X.image e))) :
    (a/2)*k'^(c*c) ≤ Fintype.card (LabelledAbsorberFamily (restrictedResourceSet R e) S X) := by
  have hloss := restricted_absorber_card_loss_scale R e S X Z he J hJ k hn hX
  let D := absorberVertexDeletionCoefficient c J (Fintype.card T)
  have hD : 0 ≤ D := by dsimp [D,absorberVertexDeletionCoefficient];positivity
  have hpow : k*k^(c*c-1)=k^(c*c) := by
    rw [← pow_succ']
    congr 1
    have hh : 1 ≤ c*c := by nlinarith
    omega
  have hloss' : (Z.card:ℝ)*D*k^(c*c-1) ≤ (a/2)*k^(c*c) := by
    calc
      _ ≤ (δ*k)*D*k^(c*c-1) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hZ hD) (by positivity)
      _ = (δ*D)*(k*k^(c*c-1)) := by ring
      _ = (δ*D)*k^(c*c) := by rw [hpow]
      _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (by positivity)
  have hnew : (a/2)*k^(c*c) ≤ Fintype.card (LabelledAbsorberFamily (restrictedResourceSet R e) S X) := by
    change _ ≤ _ + (Z.card:ℝ)*D*k^(c*c-1) at hloss
    linarith
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk' hkk' _) (by positivity)).trans hnew

theorem restricted_individual_weight_scale (d : ℕ) (b B k k' w : ℝ)
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hk' : 0 < k') (hkk' : k' ≤ k) (hhalf : k ≤ 2*k')
    (hw : b/k^d ≤ w ∧ w ≤ B/k^d) :
    (b/(2:ℝ)^d)/k'^d ≤ w ∧ w ≤ B/k'^d := by
  have hk : 0 < k := hk'.trans_le hkk'
  constructor
  · have hh : k^d ≤ (2:ℝ)^d*k'^d := by simpa only [mul_pow] using pow_le_pow_left₀ hk.le hhalf d
    have he : (b/(2:ℝ)^d)/k'^d=b/((2:ℝ)^d*k'^d) := by ring
    rw [he]
    exact (div_le_div_of_nonneg_left hb (by positivity) hh).trans hw.1
  · exact hw.2.trans (div_le_div_of_nonneg_left hB (by positivity) (pow_le_pow_left₀ hk'.le hkk' d))

end Oberwolfach
