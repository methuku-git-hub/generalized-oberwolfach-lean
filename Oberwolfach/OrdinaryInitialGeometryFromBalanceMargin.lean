module

public import Oberwolfach.OrdinaryInitialMatchingMarginsAt

@[expose] public section
/-! The already selected initial balance margin also bounds the physical
edit term in the first-level sharp geometry. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_initial_geometry_from_balance_margin
    {V U:Type} [Fintype V] [Fintype U]
    (I:Finset V) (B:Finset U) (p β εR εH L η γ:ℝ)
    (hp:0≤p) (hβ:0≤β) (hεR:0≤εR) (hεH:0≤εH) (hη:0≤η) (hηγ:η≤γ/1000)
    (hmargin:p*β*I.card+εR*I.card+2*(εH*B.card)+3*L≤η*I.card):
    3*L≤(γ/1000)*Fintype.card V :=by
  have hI:(I.card:ℝ)≤Fintype.card V:=by exact_mod_cast Finset.card_le_univ I
  have hI0:(0:ℝ)≤I.card:=by positivity
  have hB0:(0:ℝ)≤B.card:=by positivity
  have hγ0:0≤γ/1000:=hη.trans hηγ
  have h1:3*L≤η*I.card:=by
    nlinarith [mul_nonneg (mul_nonneg hp hβ) hI0,mul_nonneg hεR hI0,mul_nonneg hεH hB0]
  have h2:η*I.card≤(γ/1000)*(I.card:ℝ):=mul_le_mul_of_nonneg_right hηγ hI0
  have h3:(γ/1000)*(I.card:ℝ)≤(γ/1000)*Fintype.card V:=mul_le_mul_of_nonneg_left hI hγ0
  exact h1.trans (h2.trans h3)
end Oberwolfach
