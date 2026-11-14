module

public import Oberwolfach.OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale

@[expose] public section
/-! A smaller fresh sampling rate preserves the already selected geometric
bounds. This lets the later certificate select its own compatible rate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_nonroot_geometry_static_sampling_rate_mono
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    (r k:ℕ) (ω βparent β b B εparent εstar η ξ ζ p p' ε f binner c:ℝ)
    (X:Finset V) (Z:Finset U) (hp':0≤p') (hpp:p'≤p)
    (hf:0≤f) (hbinner:0≤binner) (hc:0≤c)
    (h:OrdinaryNonrootGeometryStatic r k ω βparent β b B εparent εstar η ξ ζ p ε f binner c X Z):
    OrdinaryNonrootGeometryStatic r k ω βparent β b B εparent εstar η ξ ζ p' ε f binner c X Z :=by
  have hcard:0≤(Fintype.card (V⊕U):ℝ):=by positivity
  have hmul:(p'+ε)*Fintype.card (V⊕U)≤(p+ε)*Fintype.card (V⊕U):=by gcongr
  have hmax:0≤max (f+binner) c:=le_trans hc (le_max_right _ _)
  have hmul2:p'*max (f+binner) c≤p*max (f+binner) c:=mul_le_mul_of_nonneg_right hpp hmax
  refine ⟨h.positive_V,h.positive_U,h.hub_lower,h.hub_upper,h.xi_nonneg,h.zeta_nonneg,hp',
    h.b_pos,h.B_nonneg,h.k_lower,h.inner_rim_size,h.inner_hub_size_V,h.inner_hub_size_U,
    hmul.trans h.reserve_scale_V,hmul.trans h.reserve_scale_U,h.degree_margin,h.isolator_margin,
    h.transfer_margin,h.weight_margin,?_⟩
  linarith only [h.balance_margin,hmul2]

theorem ordinary_vortex_buffered_root_static_geometry_sampling_rate_mono
    (r k buffer:ℕ) (ρ₀ βparent b B εparent gap βout ξ ζ edit p p' η eps γ:ℝ)
    (hp':0≤p') (hpp:p'≤p)
    (h:OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale r k buffer ρ₀ βparent b B εparent gap
      βout ξ ζ edit p η eps γ):
    OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale r k buffer ρ₀ βparent b B εparent gap
      βout ξ ζ edit p' η eps γ :=by
  intro V U _ _ _ _ P D vsize β ε lam Q hreg hn hD hρlo hρhi hβ0 hβ1 hε hv
    hlam hlam1 hlamρ hεξ hερ hεroot i hi X T Z W A C Xf Zf
    f binner c ell hf hbinner hc hell hf' hbinner' hc' hell'
  obtain ⟨hroot,hstatic,hV,hU⟩:=h V U P D vsize β ε lam Q hreg hn hD hρlo hρhi hβ0 hβ1 hε hv
    hlam hlam1 hlamρ hεξ hερ hεroot i hi f binner c ell hf hbinner hc hell hf' hbinner' hc' hell'
  have hcard:0≤(Fintype.card (A⊕C):ℝ):=by positivity
  have hmul:(p'+eps)*Fintype.card (A⊕C)≤(p+eps)*Fintype.card (A⊕C):=by gcongr
  refine ⟨hroot,ordinary_nonroot_geometry_static_sampling_rate_mono r k (ρ₀/16) βparent βout b B εparent
    (εparent+gap) η ξ ζ p p' eps f binner c Xf Zf hp' hpp hf hbinner hc hstatic,?_,?_⟩
  · linarith only [hV,hmul]
  · linarith only [hU,hmul]
end Oberwolfach
