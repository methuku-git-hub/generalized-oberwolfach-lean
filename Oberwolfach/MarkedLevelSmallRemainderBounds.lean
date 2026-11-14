module

public import Oberwolfach.MarkedFixedVortexSizes

@[expose] public section
/-! Numerical consequences of the nested-set size estimates. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_level_small_remainder_bounds
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (I T:Finset V) (J R:Finset U) (ε κ hcut ξ:ℝ)
    (he:0≤ε) (hehalf:ε≤1/2) (hek:ε≤κ) (hec:ε≤hcut) (hex:ε≤ξ)
    (hT:(T.card:ℝ)≤ε*I.card) (hR:(R.card:ℝ)≤ε*J.card)
    (hJ:(J.card:ℝ)≤Fintype.card V):
    (T.card:ℝ)≤κ*Fintype.card V ∧ (R.card:ℝ)≤κ*Fintype.card V ∧
    (T.card:ℝ)≤hcut*I.card ∧ (R.card:ℝ)≤hcut*J.card ∧
    (T.card:ℝ)≤ξ*Fintype.card V ∧ (R.card:ℝ)≤ξ*Fintype.card V ∧
    (Fintype.card V:ℝ)/2≤(Fintype.card ↥((Finset.univ\T):Finset V):ℝ):=by
  have hI:(I.card:ℝ)≤Fintype.card V:=by exact_mod_cast (Finset.card_le_univ I)
  have hN:(0:ℝ)≤Fintype.card V:=Nat.cast_nonneg _
  have hI0:(0:ℝ)≤I.card:=Nat.cast_nonneg _
  have hJ0:(0:ℝ)≤J.card:=Nat.cast_nonneg _
  have hTL:(T.card:ℝ)≤ε*Fintype.card V:=hT.trans (mul_le_mul_of_nonneg_left hI he)
  have hRL:(R.card:ℝ)≤ε*Fintype.card V:=hR.trans (mul_le_mul_of_nonneg_left hJ he)
  have hcomp:(Fintype.card ↥((Finset.univ\T):Finset V):ℝ)=Fintype.card V-T.card:=by
    rw [Fintype.card_coe,Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,Nat.cast_sub (Finset.card_le_univ T)]
  refine ⟨hTL.trans (mul_le_mul_of_nonneg_right hek hN),hRL.trans (mul_le_mul_of_nonneg_right hek hN),
    hT.trans (mul_le_mul_of_nonneg_right hec hI0),hR.trans (mul_le_mul_of_nonneg_right hec hJ0),
    hTL.trans (mul_le_mul_of_nonneg_right hex hN),hRL.trans (mul_le_mul_of_nonneg_right hex hN),?_⟩
  rw [hcomp]
  nlinarith [mul_nonneg (sub_nonneg.mpr hehalf) hN]
end Oberwolfach
