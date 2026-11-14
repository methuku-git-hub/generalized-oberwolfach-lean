module

public import Oberwolfach.VortexSamplingDomainSizes

@[expose] public section
/-! The actual fixed vortex has at most the ambient number of levels, so
its finite-family probability bound can use exponent one. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_fixed_vortex_level_count
    {V U:Type} [Fintype V] [Fintype U] {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ}
    (Q:Vortex U G D β ε m) (he:0<ε) (he1:ε<1) (hm:0<m)
    (L:ℕ) (hL:L<Q.length):
    (L+1:ℝ)≤(Fintype.card V:ℝ)^(1:ℝ):=by
  have hh:=Q.number_of_levels_le_order he he1 hm
  have hnat:L+1≤Fintype.card V:=by omega
  have hreal:(L+1:ℝ)≤Fintype.card V:=by exact_mod_cast hnat
  simpa only [Real.rpow_one] using hreal
end Oberwolfach
