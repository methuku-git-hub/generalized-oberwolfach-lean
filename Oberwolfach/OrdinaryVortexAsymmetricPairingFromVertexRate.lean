module

public import Oberwolfach.OrdinaryVortexAsymmetricPairingGeometryProp

@[expose] public section
/-! Convert the vertex-scale edit bound supplied by the actual protected
trace to the whole local-domain bound used by the pairing certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_asymmetric_pairing_from_vertex_rate
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    {G:SimpleGraph V} {D mv:ℕ} {β ε:ℝ}
    (Q:Vortex U G D β ε mv)
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:(Fintype.card V:ℝ)/2≤D)
    {ρ₀:ℝ} (hρ:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hm:0<mv) (i:ℕ) (hi:i<Q.length)
    (Ncert N:ℕ) (hN:Ncert≤N) (hsize:2/ε≤N) (hterminal:(N:ℝ)≤ε*mv/2)
    (δend εR εH rateParent ζ Ledit:ℝ) (hδ:0≤δend)
    (hR:εR≤δend/4) (hH:εH≤δend/4) (hRate:rateParent≤δend*ε/8)
    (hRate0:0≤rateParent) (hζ:ζ≤rateParent)
    (hEdit:Ledit≤ζ*Fintype.card (markedVortexVertexType Q i))
    (ζh ζe γ eCoeff:ℝ) (hζh:0<ζh) (hζe:0<ζe) (hγ:0<γ) (he:γ≤eCoeff):
    OrdinaryVortexAsymmetricPairingGeometryAt Q i Ncert ρ₀ δend εR εH Ledit ζh ζe γ eCoeff :=by
  have hnle:(Fintype.card (markedVortexVertexType Q i):ℝ)≤
      Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i):=by
    exact_mod_cast Fintype.card_le_of_injective Sum.inl Sum.inl_injective
  have hEdit':Ledit≤rateParent*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i):=
    hEdit.trans ((mul_le_mul_of_nonneg_right hζ (by positivity)).trans (mul_le_mul_of_nonneg_left hnle hRate0))
  exact ordinary_vortex_asymmetric_pairing_geometry_at Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hm i hi
    Ncert N hN hsize hterminal δend εR εH rateParent Ledit hδ hR hH hRate hEdit' ζh ζe γ eCoeff hζh hζe hγ he
end Oberwolfach
