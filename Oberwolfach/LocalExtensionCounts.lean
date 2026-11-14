module

public import Oberwolfach.EndpointRelativeCounts
public import Oberwolfach.ThresholdComparisons

@[expose] public section

/-! Lower bounds for the actual extension sets, including external roots.
The conflict-neighbour loss precedes multiplication by the supplied density. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type*} [Fintype V] [DecidableEq V] [DecidableEq U]

def ordinaryExtensionRootBound (r : ℕ) : ℕ := if r=3 then 4 else if r=4 then 3 else 2

theorem ordinaryExtensionRootBound_range (r : ℕ) :
    1≤ordinaryExtensionRootBound r ∧ ordinaryExtensionRootBound r≤4 := by
  unfold ordinaryExtensionRootBound
  split_ifs <;> omega

theorem ordinaryExtensionRootBound_threshold (r : ℕ) (hr : 3≤r) :
    1-1/(ordinaryExtensionRootBound r:ℝ)≤cycleThreshold r := by
  by_cases h3:r=3
  · subst r
    convert cycleThreshold_triangle_lower using 1 <;> norm_num [ordinaryExtensionRootBound]
  by_cases h4:r=4
  · subst r
    convert cycleThreshold_four_lower using 1 <;> norm_num [ordinaryExtensionRootBound]
  convert cycleThreshold_half_le hr using 1 <;> norm_num [ordinaryExtensionRootBound,h3,h4]

theorem extension_parent_common_lower (P F : SimpleGraph V) (A X : Finset V)
    (k : ℕ) (γ L : ℝ) (hk : 1≤k) (hγ : 0<γ) (hγ1 : γ≤1) (hL : 0≤L)
    (hX : X.card≤k) (hloss : (k:ℝ)*L≤γ*A.card/2)
    (hdeg : ∀ v∈X,(1-1/(k:ℝ)+γ)*A.card≤((A∩P.neighborFinset v).card:ℝ))
    (hF : ∀ v∈X,(F.degree v:ℝ)≤L) :
    γ*A.card/2≤((common A X (fun v=>(P\F).neighborFinset v)).card:ℝ) := by
  have hkpos : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hXr : (X.card:ℝ)≤k := by exact_mod_cast hX
  have hcoef : γ≤1-(X.card:ℝ)*(1-(1-1/(k:ℝ)+γ)) := by
    by_cases hzero:X.card=0
    · simp [hzero,hγ1]
    · have hXpos : (1:ℝ)≤X.card := by exact_mod_cast (show 1≤X.card by omega)
      have hfrac : (X.card:ℝ)/(k:ℝ)≤1 := (div_le_one₀ hkpos).mpr hXr
      have hmul:=mul_le_mul_of_nonneg_right hXpos hγ.le
      have he : 1-(X.card:ℝ)*(1-(1-1/(k:ℝ)+γ))=1-(X.card:ℝ)/(k:ℝ)+X.card*γ := by ring
      rw [he]
      linarith only [hfrac,hmul]
  have hh:=common_neighbour_deletion_lower P F A X (1-1/(k:ℝ)+γ) L hdeg hF
  have hm:=mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg A.card)
  have hl:=mul_le_mul_of_nonneg_right hXr hL
  linarith only [hh,hm,hl,hloss]

theorem extension_relative_row_lower (P R F : SimpleGraph V) (A X : Finset V)
    (J : Finset U) (N : U→Finset V) (k : ℕ) (γ p q s ε L : ℝ)
    (hk : 1≤k) (hk4 : k≤4) (hγ : 0<γ) (hγ1 : γ≤1)
    (hp : 0<p) (hp1 : p≤1) (hq : p≤q) (hs : p≤s) (hL : 0≤L)
    (hX : X.card≤k) (hJ : J.card≤2) (hloss : (k:ℝ)*L≤γ*A.card/2)
    (hε : ε≤p^6*γ/4)
    (hdeg : ∀ v∈X,(1-1/(k:ℝ)+γ)*A.card≤((A∩P.neighborFinset v).card:ℝ))
    (hF : ∀ v∈X,(F.degree v:ℝ)≤L)
    (hrelative : q^X.card*s^J.card*((common A X (fun v=>(P\F).neighborFinset v)).card:ℝ)-ε*A.card≤
      ((common (common A X (fun v=>R.neighborFinset v)) J N).card:ℝ)) :
    (p^6*γ/4)*A.card≤((common (common A X (fun v=>R.neighborFinset v)) J N).card:ℝ) := by
  have hc:=extension_parent_common_lower P F A X k γ L hk hγ hγ1 hL hX hloss hdeg hF
  have hprod : p^6≤q^X.card*s^J.card := by
    calc
      _ ≤ p^(X.card+J.card) := pow_le_pow_of_le_one hp.le hp1 (by omega)
      _ = p^X.card*p^J.card := pow_add _ _ _
      _ ≤ _ := mul_le_mul (pow_le_pow_left₀ hp.le hq _) (pow_le_pow_left₀ hp.le hs _)
        (pow_nonneg hp.le _) (pow_nonneg (hp.le.trans hq) _)
  have hm:=mul_le_mul hprod hc (by positivity : 0≤γ*A.card/2)
    (mul_nonneg (pow_nonneg (hp.le.trans hq) _) (pow_nonneg (hp.le.trans hs) _))
  have he:=mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg A.card)
  nlinarith only [hm,he,hrelative]

theorem extension_relative_index_lower [Fintype U] (B : Finset U) (X : Finset V)
    (N : V→Finset U) (r : ℕ) (p s ε : ℝ) (hp : 0<p) (hp1 : p≤1)
    (hs : p≤s) (hX : X.card≤r+6) (hε : ε≤p^(r+6)/2)
    (hrelative : (s^X.card-ε)*B.card≤((common B X N).card:ℝ)) :
    (p^(r+6)/2)*B.card≤((common B X N).card:ℝ) := by
  have hpow : p^(r+6)≤s^X.card :=
    (pow_le_pow_of_le_one hp.le hp1 hX).trans (pow_le_pow_left₀ hp.le hs _)
  exact (mul_le_mul_of_nonneg_right (by linarith only [hpow,hε]) (Nat.cast_nonneg B.card)).trans hrelative

end Oberwolfach
