module

public import Oberwolfach.OrdinaryCleanupFixedMarginsHierarchy

@[expose] public section
/-! A small later edit scale supplies the four numerical inequalities for
    the earlier fixed cleanup margins. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_cleanup_fixed_scaled_bounds
    (p₀ gap κinner lam εR εH ζ I B L:ℝ)
    (hp:0<p₀) (hgap:0<gap) (hκ:0<κinner) (hI:0≤I) (hB:0≤B) (hBI:B≤I)
    (hεR0:0≤εR) (hεR:εR≤lam) (hεH0:0≤εH) (hεH:εH≤lam)
    (hζ:ζ≤lam) (hL:L≤ζ*I)
    (hcapE:lam≤(p₀^3*gap)/12) (hcapH:lam≤(p₀^2*κinner)/8):
    εR*I≤(p₀^3*gap)*I/4 ∧ 3*L≤(p₀^3*gap)*I/4 ∧
      εH*B≤(p₀^2*κinner)*I/4 ∧ 2*L≤(p₀^2*κinner)*I/4 :=by
  have hRI:=mul_le_mul_of_nonneg_right hεR hI
  have hHI:=mul_le_mul_of_nonneg_right hεH hI
  have hHB:=mul_le_mul_of_nonneg_left hBI hεH0
  have hLI:=hL.trans (mul_le_mul_of_nonneg_right hζ hI)
  have hE:=mul_le_mul_of_nonneg_right hcapE hI
  have hH:=mul_le_mul_of_nonneg_right hcapH hI
  have hE0:0≤(p₀^3*gap)*I:=by positivity
  have hH0:0≤(p₀^2*κinner)*I:=by positivity
  constructor
  · nlinarith only [hRI,hE,hE0]
  constructor
  · nlinarith only [hLI,hE]
  constructor
  · nlinarith only [hHI,hHB,hH,hH0]
  · nlinarith only [hLI,hH]
end Oberwolfach
