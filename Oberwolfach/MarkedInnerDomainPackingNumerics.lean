module

public import Oberwolfach.MarkedInnerPrescribedEdgePacking
public import Oberwolfach.MarkedInnerPackingNumerics

@[expose] public section

/-! Explicit budgets for packing outside edges through the inner pair.
The extension counts are measured on that pair; its complement is never
charged as a forbidden set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_inner_domain_packing_numeric_budgets
    (L q k dr ds nr ns sep B:ℝ) (hL:0≤L) (hq:0<q) (hB:0<B)
    (hklo:q≤k) (hkhi:k≤2*q) (hdr:dr≤q) (hds:ds≤q)
    (hnr:nr≤q^2) (hns:ns≤q^2)
    (hsep:sep≤B/10) (hqB:100*(L+20)*q≤B):
    (nr*(L+5)/k+k*(L+5)+sep+8*(k+dr)<B)∧
    (nr/k+2*(k+dr)<B)∧
    (ns*(L+5)/k+ds*(L+5)+sep+8*(k+ds)+8*(k+dr)<B):=by
  have hk:0<k:=hq.trans_le hklo
  have hLf:0≤L+5:=by linarith
  have hrdiv:nr/k≤q:=by
    apply (div_le_iff₀ hk).mpr
    nlinarith only [hnr,mul_le_mul_of_nonneg_left hklo hq.le]
  have hsdiv:ns/k≤q:=by
    apply (div_le_iff₀ hk).mpr
    nlinarith only [hns,mul_le_mul_of_nonneg_left hklo hq.le]
  have hrdiv':nr*(L+5)/k≤q*(L+5):=by
    convert mul_le_mul_of_nonneg_right hrdiv hLf using 1 <;> ring
  have hsdiv':ns*(L+5)/k≤q*(L+5):=by
    convert mul_le_mul_of_nonneg_right hsdiv hLf using 1 <;> ring
  have hdsm:ds*(L+5)≤q*(L+5):=mul_le_mul_of_nonneg_right hds hLf
  have hkm:k*(L+5)≤2*q*(L+5):=mul_le_mul_of_nonneg_right hkhi hLf
  have hlq:0≤L*q:=mul_nonneg hL hq.le
  constructor
  · nlinarith only [hrdiv',hkm,hsep,hkhi,hdr,hqB,hB,hq,hlq]
  constructor
  · nlinarith only [hrdiv,hkhi,hdr,hqB,hB,hq,hlq]
  · nlinarith only [hsdiv',hdsm,hsep,hkhi,hds,hdr,hqB,hB,hq,hlq]
theorem marked_inner_domain_order_threshold (l:ℕ) (β:ℝ) (hβ:0<β)
    (η:ℝ) (hη:0<η) (hη1:η≤1) (hscale:100*((l:ℝ)+20)*η≤β) (b:ℕ):
    ∃ n₀:ℕ,∀ n:ℕ,n₀≤n→
      (0<n)∧(1≤η*n)∧(η≤1)∧
      (100*((l:ℝ)+20)*(η*n)≤β*n)∧(((l:ℝ)+6)*(2*b+1)≤β*n/10)∧
      (η*n≤(Nat.ceil (η*n):ℝ))∧((Nat.ceil (η*n):ℝ)≤2*(η*n)):=by
  obtain ⟨n₀,hn₀⟩:=exists_nat_gt (max (1/η) (10*(((l:ℝ)+6)*(2*b+1))/β))
  refine ⟨n₀,?_⟩
  intro n hn
  have hnreal:(n₀:ℝ)≤n:=by exact_mod_cast hn
  have ha:1/η<(n:ℝ):=(le_max_left _ _).trans_lt (hn₀.trans_le hnreal)
  have hb:10*(((l:ℝ)+6)*(2*b+1))/β<(n:ℝ):=(le_max_right _ _).trans_lt (hn₀.trans_le hnreal)
  have hηn:1<η*n:=by have hh:1<(n:ℝ)*η:=(div_lt_iff₀ hη).mp ha;nlinarith only [hh]
  have hnn:(0:ℝ)<n:=lt_trans (by positivity : (0:ℝ)<1/η) ha
  have hceil:η*n≤(Nat.ceil (η*n):ℝ):=Nat.le_ceil _
  have hceil':(Nat.ceil (η*n):ℝ)<η*n+1:=Nat.ceil_lt_add_one (by positivity)
  refine ⟨by exact_mod_cast hnn,hηn.le,hη1,?_,?_,hceil,?_⟩
  · nlinarith only [mul_le_mul_of_nonneg_right hscale hnn.le]
  · have hh:10*(((l:ℝ)+6)*(2*b+1))<(n:ℝ)*β:=(div_lt_iff₀ hβ).mp hb
    nlinarith only [hh]
  · linarith only [hceil',hηn]

end Oberwolfach
