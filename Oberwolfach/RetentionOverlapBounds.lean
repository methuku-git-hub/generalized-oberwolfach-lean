module

public import Oberwolfach.EqualizedJointRetention
public import Oberwolfach.SymmetricLocalLemma

@[expose] public section

/-! Quantitative bounds for the exact overlap factor in joint retention.
The estimate is useful while the lists are long compared with the overlap. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem one_sub_inverse_pow_lower {l n : ℕ} (hl : 0<l) :
    1-(n : ℝ)/(l : ℝ)≤(1-1/(l : ℝ))^n := by
  have hlr : (1 : ℝ)≤l := by exact_mod_cast hl
  have h := finite_product_one_sub_lower (Finset.range n) (fun _=>(1 : ℝ)/(l : ℝ))
    (fun _ _=>⟨by positivity,(div_le_one (by positivity)).mpr hlr⟩)
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Finset.prod_const,
    mul_one_div] using h

theorem inverse_power_overlap_bound
    {l n M : ℕ} (hl : 1<l) (hn : n≤M) (hM : 2*M≤l)
    {b : ℝ} (hb : 0≤b) :
    b≤b/(1-1/(l : ℝ))^n ∧
      b/(1-1/(l : ℝ))^n≤(1+2*(M : ℝ)/(l : ℝ))*b := by
  let r : ℝ := (M : ℝ)/(l : ℝ)
  let q : ℝ := 1-1/(l : ℝ)
  have hlr : (1 : ℝ)<l := by exact_mod_cast hl
  have hlpos : (0 : ℝ)<l := by positivity
  have hqpos : 0<q := sub_pos.mpr ((div_lt_one hlpos).mpr hlr)
  have hqone : q≤1 := sub_le_self _ (by positivity)
  have hpowpos : 0<q^n := pow_pos hqpos _
  have hpowone : q^n≤1 := pow_le_one₀ hqpos.le hqone
  have hr0 : 0≤r := by positivity
  have hrhalf : r≤1/2 := by
    apply (div_le_iff₀ hlpos).mpr
    have hh : (2 : ℝ)*M≤l := by exact_mod_cast hM
    linarith
  have hden : 1-r≤q^n := by
    have h := one_sub_inverse_pow_lower (l:=l) (n:=n) (by omega)
    have hnm : (n : ℝ)/(l : ℝ)≤(M : ℝ)/(l : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hn) hlpos.le
    dsimp [q,r]
    linarith
  have hprod : 1≤(1+2*r)*(1-r) := by
    have hh := mul_nonneg hr0 (show 0≤1-2*r by linarith)
    nlinarith
  constructor
  · exact (le_div_iff₀ hpowpos).mpr (by nlinarith [mul_le_mul_of_nonneg_left hpowone hb])
  · change b/q^n≤_
    rw [show (1+2*(M : ℝ)/(l : ℝ))=1+2*r from by dsimp [r];ring]
    apply (div_le_iff₀ hpowpos).mpr
    calc
      b = b*1 := by ring
      _ ≤ b*((1+2*r)*(1-r)) := mul_le_mul_of_nonneg_left hprod hb
      _ = ((1+2*r)*b)*(1-r) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hden (mul_nonneg (by positivity) hb)

theorem equalized_joint_retention_bounds
    {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]
    (G : SimpleGraph V) (L : V → Finset C) (hL : ∀ v,(L v).Nonempty)
    {l K B : ℕ} (hl : 1<l) (hcard : ∀ v,(L v).card=l)
    (S : Finset V) (hS : ∀ u∈S,∀ v∈S,¬G.Adj u v) (c : C)
    (hc : ∀ v∈S,c∈L v)
    (hbound : ∀ v∈S,(colourNeighbourSet G L v c).card≤K)
    (hpair : ∀ u∈S,∀ v∈S,u≠v →
      (colourNeighbourSet G L u c∩colourNeighbourSet G L v c).card≤B)
    (hsmall : 2*(S.card^2*B)≤l) :
    let p := (FiniteLaw.pi (fun u=>(FiniteLaw.uniformOn (L u) (hL u)).withCoin
      (equalizationCoin G L l K u)
      (equalizationCoin_bounds G L (by omega) K u))).probability
      (fun σ=>∀ v∈S,coinRetainedColour G σ v=some c)
    let b := (((1-1/(l : ℝ))^K)/(l : ℝ))^S.card
    b≤p ∧ p≤(1+2*((S.card^2*B : ℕ) : ℝ)/(l : ℝ))*b := by
  dsimp only
  rw [equalized_joint_retention G L hL hl hcard S hS c hc hbound]
  apply inverse_power_overlap_bound hl
    (finiteUnionOverlap_le S (fun v=>colourNeighbourSet G L v c) hpair) hsmall
  have hlr : (1 : ℝ)≤l := by exact_mod_cast (show 1≤l by omega)
  have hq : 0≤1-1/(l : ℝ) :=
    sub_nonneg.mpr ((div_le_one (by positivity)).mpr hlr)
  exact pow_nonneg (div_nonneg (pow_nonneg hq _) (Nat.cast_nonneg _)) _

end Oberwolfach
