module

public import Oberwolfach.MarkedRowPackingNumerics

@[expose] public section

/-! The free-use cap and all error/deletion allowances precede the
permutation radius. Only the order threshold absorbs its additive cost. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach

theorem marked_successive_row_numeric_threshold (l : ℕ) (β p₀ a : ℝ)
    (hβ : 0<β) (hp₀ : 0<p₀) (ha : 0<a) :
    ∃ K : ℕ,0<K ∧ ∃ eta kappa : ℝ,0<eta ∧ 0<kappa ∧ eta≤p₀*a/32 ∧
    ∀ b : ℕ,∃ N₀ : ℕ,∀ N r h s : ℕ,N₀≤N →
      (r:ℝ)≤kappa*N → (h:ℝ)≤kappa*N → (s:ℝ)≤N → ∀ q : ℝ,q≤kappa*N →
      let loss : ℝ := (r*max (K+4) (l+4):ℕ)
      (r*(K+4):ℕ)≤loss ∧ (r*(l+4):ℕ)≤loss ∧
      loss≤(p₀/4)*(eta*N) ∧ (p₀*a/4)*N+loss≤(p₀*a/2)*N ∧
      2*(eta*N)+(2*(2*b+1):ℕ)≤(p₀*a/4)*N ∧
      (2*(2*b+1):ℕ)<(p₀/4)*(eta*N) ∧
      q+(s*(l+4):ℕ)/(K:ℝ)+(l+5)*(2*b+1)+8*(K+4:ℕ)+
        2*(r*(4*(K+4)):ℕ)+2*(r*(l+4):ℕ)+4*h<β*N := by
  obtain ⟨K,hK,hbase⟩ := marked_row_packing_numeric_threshold l (β/2) 1 (by positivity) (by norm_num)
  let eta := p₀*a/32
  let D : ℝ := (max (K+4) (l+4):ℕ)
  let C : ℝ := 8*(K+4:ℕ)+2*(l+4:ℕ)+4
  let kappa := min (β/(8*(C+1))) (min (p₀*eta/(8*(D+1))) (p₀*a/(8*(D+1))))
  have heta : 0<eta := by dsimp [eta];positivity
  have hD : 0≤D := by dsimp [D];positivity
  have hC : 0≤C := by dsimp [C];positivity
  have hkappa : 0<kappa := by dsimp [kappa];positivity
  have hkβ : kappa*(C+1)≤β/8 := by
    have h:=min_le_left (β/(8*(C+1))) (min (p₀*eta/(8*(D+1))) (p₀*a/(8*(D+1))))
    have hh := (le_div_iff₀ (by positivity : 0<8*(C+1))).mp h
    change kappa*(8*(C+1))≤β at hh
    nlinarith only [hh]
  have hkcut : kappa*(D+1)≤p₀*eta/8 := by
    have h : kappa≤p₀*eta/(8*(D+1)) := (min_le_right _ _).trans (min_le_left _ _)
    have hh := (le_div_iff₀ (by positivity : 0<8*(D+1))).mp h
    nlinarith only [hh]
  have hkdeg : kappa*(D+1)≤p₀*a/8 := by
    have h : kappa≤p₀*a/(8*(D+1)) := (min_le_right _ _).trans (min_le_right _ _)
    have hh := (le_div_iff₀ (by positivity : 0<8*(D+1))).mp h
    nlinarith only [hh]
  have hkβ' : kappa≤β/8 := by nlinarith only [hkβ,mul_nonneg hkappa.le hC]
  refine ⟨K,hK,eta,kappa,heta,hkappa,le_rfl,?_⟩
  intro b
  obtain ⟨Nbase,hbaseN⟩ := hbase b 2
  let B : ℝ := 2*b+1
  obtain ⟨Nlarge,hlarge⟩ := exists_nat_gt (max 1 (max (32*B/(p₀*a)) (8*B/(p₀*eta))))
  refine ⟨max Nbase Nlarge,?_⟩
  intro N r h s hN hr hh hs q hq loss
  have hNbase : Nbase≤N := (le_max_left _ _).trans hN
  have hNlarge : (Nlarge:ℝ)≤N := Nat.cast_le.mpr ((le_max_right _ _).trans hN)
  have hNpos : (0:ℝ)<N := by have ht:=(le_max_left _ _).trans_lt (hlarge.trans_le hNlarge);linarith
  have hBN : 32*B<(N:ℝ)*(p₀*a) :=
    (div_lt_iff₀ (by positivity)).mp (((le_max_left _ _).trans (le_max_right _ _)).trans_lt (hlarge.trans_le hNlarge))
  have hBM : 8*B<(N:ℝ)*(p₀*eta) :=
    (div_lt_iff₀ (by positivity)).mp (((le_max_right _ _).trans (le_max_right _ _)).trans_lt (hlarge.trans_le hNlarge))
  have hqβ : q≤(β/2)*N/4 := by
    have ht := mul_le_mul_of_nonneg_right hkβ' hNpos.le
    nlinarith only [hq,ht]
  have hbas := hbaseN N s hNbase (by simpa using hs) q hqβ
  have hloss : loss≤kappa*D*N := by
    have ht := mul_le_mul_of_nonneg_right hr hD
    dsimp [loss,D] at ht ⊢
    push_cast at ht ⊢
    nlinarith only [ht]
  have hlcut : loss≤p₀*eta*N/8 := by
    have ht := mul_le_mul_of_nonneg_right hkcut hNpos.le
    nlinarith only [hloss,ht,mul_nonneg hkappa.le hNpos.le]
  have hldeg : loss≤p₀*a*N/8 := by
    have ht := mul_le_mul_of_nonneg_right hkdeg hNpos.le
    nlinarith only [hloss,ht,mul_nonneg hkappa.le hNpos.le]
  have hextra : 2*(r*(4*(K+4)):ℕ)+2*(r*(l+4):ℕ)+4*(h:ℝ)≤β*N/8 := by
    have hrC := mul_le_mul_of_nonneg_right hr (show (0:ℝ)≤8*(K+4:ℕ)+2*(l+4:ℕ) by positivity)
    have hhC := mul_le_mul_of_nonneg_right hh (show (0:ℝ)≤4 by norm_num)
    have ht := mul_le_mul_of_nonneg_right hkβ hNpos.le
    dsimp [C] at ht
    push_cast at hrC ht ⊢
    nlinarith only [hrC,hhC,ht,mul_nonneg hkappa.le hNpos.le]
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · dsimp [loss]
    exact_mod_cast Nat.mul_le_mul_left r (le_max_left (K+4) (l+4))
  · dsimp [loss]
    exact_mod_cast Nat.mul_le_mul_left r (le_max_right (K+4) (l+4))
  · nlinarith only [hlcut,mul_pos (mul_pos hp₀ heta) hNpos]
  · nlinarith only [hldeg,mul_pos (mul_pos hp₀ ha) hNpos]
  · dsimp [eta,B] at hBN ⊢
    push_cast
    nlinarith only [hBN,mul_pos (mul_pos hp₀ ha) hNpos]
  · dsimp [B] at hBM
    push_cast
    nlinarith only [hBM]
  · norm_num only [Nat.mul_zero,Nat.mul_one,Nat.reduceMul] at hbas
    nlinarith only [hbas,hextra,mul_pos hβ hNpos]

end Oberwolfach
