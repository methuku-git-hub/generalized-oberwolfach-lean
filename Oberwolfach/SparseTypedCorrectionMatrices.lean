module

public import Oberwolfach.TypedDegreeDemandArithmetic
public import Oberwolfach.TypedCorrectionScales

@[expose] public section

/-! Uniform parameters for the four integral typed correction matrices. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sparse_typed_correction_matrices (q : ℕ) (hq : 1≤q) (ω h δ ξ : ℝ)
    (hω : 0<ω) (hδ : 0<δ) (hδsmall : δ<1/4) (hξ : 0<ξ)
    (hξh : ((q:ℝ)+1)*ξ≤h/100) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∃ n₀ : ℕ,∀ η : ℝ,0≤η → η≤η₀ →
    ∀ (V U : Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      n₀≤Fintype.card V → ω*Fintype.card V≤Fintype.card U → Fintype.card U≤Fintype.card V →
    ∀ (A₀ Aₖ : V → V → ℕ) (H₀ Hₖ : V → U → ℕ)
      (bp bm bk : V → ℤ) (bw : U → ℤ),
      (∑ v,bp v=∑ v,bm v) →
      (∀ v,|(bp v : ℝ)|≤η*Fintype.card V) →
      (∀ v,|(bm v : ℝ)|≤η*Fintype.card V) →
      (∀ v,|(bk v : ℝ)|≤η*Fintype.card V) →
      (∀ u,|(bw u : ℝ)|≤η*Fintype.card V) →
      BipartiteLargeCut A₀ δ h → BipartiteLargeCut Aₖ δ h →
      BipartiteLargeCut H₀ δ h → BipartiteLargeCut Hₖ δ h →
    ∃ (J₀ Jₖ : V → V → ℕ) (L₀ Lₖ : V → U → ℕ),
      (∀ x y,J₀ x y≤A₀ x y) ∧ (∀ x y,Jₖ x y≤Aₖ x y) ∧
      (∀ v u,L₀ v u≤H₀ v u) ∧ (∀ v u,Lₖ v u≤Hₖ v u) ∧
      (∀ v,(∑ x,(J₀ v x : ℤ))+(∑ x,(Jₖ v x : ℤ))-
        (∑ u,(L₀ v u : ℤ))-(∑ u,(Lₖ v u : ℤ))=bp v) ∧
      (∀ v,(∑ x,(J₀ x v : ℤ))+(∑ x,(Jₖ x v : ℤ))-
        (∑ u,(L₀ v u : ℤ))-(∑ u,(Lₖ v u : ℤ))=bm v) ∧
      (∀ v,(∑ x,(Jₖ x v : ℤ))-(∑ u,(Lₖ v u : ℤ))=bk v) ∧
      (∀ u,(∑ v,(L₀ v u : ℤ))-(q:ℤ)*(∑ v,(Lₖ v u : ℤ))=bw u) ∧
      (∀ v,(∑ x,(J₀ v x : ℝ))≤2*((q:ℝ)+1)*ξ*Fintype.card V ∧
        (∑ x,(J₀ x v : ℝ))≤2*((q:ℝ)+1)*ξ*Fintype.card V ∧
        (∑ x,(Jₖ v x : ℝ))≤2*((q:ℝ)+1)*ξ*Fintype.card V ∧
        (∑ x,(Jₖ x v : ℝ))≤2*((q:ℝ)+1)*ξ*Fintype.card V ∧
        (∑ u,(L₀ v u : ℝ))≤2*((q:ℝ)+1)*ξ*Fintype.card V ∧
        (∑ u,(Lₖ v u : ℝ))≤2*((q:ℝ)+1)*ξ*Fintype.card V) ∧
      (∀ u,(∑ v,(L₀ v u : ℝ))≤2*((q:ℝ)+1)*ξ*Fintype.card V ∧
        (∑ v,(Lₖ v u : ℝ))≤2*((q:ℝ)+1)*ξ*Fintype.card V) := by
  obtain ⟨N,hN,hscale⟩ := sparse_correction_order_threshold 0 hδ hω hξ
  refine ⟨δ*ω*ξ/1000,by positivity,N,?_⟩
  intro η hη hηsmall V U _ _ _ _ hn hωn hsn A₀ Aₖ H₀ Hₖ bp bm bk bw htot hbp hbm hbk hbw hcut0 hcutK hcutH0 hcutHK
  let n := Fintype.card V
  have hn1 : 1≤n := hN.trans hn
  have hnpos : 0<n := by omega
  have hnR : (0:ℝ)<n := by exact_mod_cast hnpos
  have hspos : 0<Fintype.card U := by
    have hh : (0:ℝ)<Fintype.card U := (mul_pos hω hnR).trans_le hωn
    exact_mod_cast hh
  have hω1 : ω≤1 := by
    have hh : (Fintype.card U : ℝ)≤n := by exact_mod_cast hsn
    nlinarith only [hωn,hh,hnR]
  let base := Nat.floor (ξ*n)
  have hnscale : 100≤δ*ω*ξ*n := by have hh := hscale n hn;norm_num at hh;linarith
  obtain ⟨hmargin,hcap,hbound⟩ := typed_correction_numeric hq hδ (by linarith : δ≤1)
    hω hω1 hξ hξh hη hηsmall hnscale
  change 3+4*(η*n)≤δ*(ω*base-3*(η*n)) at hmargin
  change (q:ℝ)*base+3*(η*n)≤h*n/2 at hcap
  change ((q:ℝ)+2)*base≤2*((q:ℝ)+1)*ξ*n at hbound
  have hmean : ω*base≤(Fintype.card U : ℝ)*base/n := by
    apply (le_div_iff₀ hnR).mpr
    nlinarith [mul_le_mul_of_nonneg_right hωn (Nat.cast_nonneg base : (0:ℝ)≤base)]
  have hmargin' : 3+4*(η*n)≤δ*((Fintype.card U : ℝ)*base/n-3*(η*n)) := by
    nlinarith [mul_le_mul_of_nonneg_left hmean hδ.le]
  obtain ⟨J₀,Jₖ,L₀,Lₖ,hJ0,hJK,hL0,hLK,hp,hm,hk,hw,hvb,hub⟩ :=
    typed_integer_correction_matrices A₀ Aₖ H₀ Hₖ hnpos hspos hsn base q hq bp bm bk bw htot
      (by positivity : 0≤η*n) hδ.le hδsmall hbp hbm hbk hbw hmargin' hcap hcut0 hcutK hcutH0 hcutHK
  refine ⟨J₀,Jₖ,L₀,Lₖ,hJ0,hJK,hL0,hLK,hp,hm,hk,hw,?_,?_⟩
  · intro v
    exact ⟨(hvb v).1.trans hbound,(hvb v).2.1.trans hbound,(hvb v).2.2.1.trans hbound,
      (hvb v).2.2.2.1.trans hbound,(hvb v).2.2.2.2.1.trans hbound,(hvb v).2.2.2.2.2.trans hbound⟩
  · intro u
    exact ⟨(hub u).1.trans hbound,(hub u).2.trans hbound⟩

end Oberwolfach
