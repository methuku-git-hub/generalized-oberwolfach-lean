module

public import Oberwolfach.OrdinaryVortexAsymmetricPairingFromVertexRate

@[expose] public section
/-! Initial pairing geometry from the inner-set edit estimate supplied by
matching and correction on the same edited host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_initial_pairing_from_inner_edit
    {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
    {P:SimpleGraph V} {D mv:ℕ} {β ε:ℝ}
    (Q:Vortex U P D β ε mv)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:(Fintype.card V:ℝ)/2≤D)
    {ρ₀:ℝ} (hρ:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hm:0<mv)
    (Ncert N:ℕ) (hN:Ncert≤N) (hsize:2/ε≤N) (hterminal:(N:ℝ)≤ε*mv/2)
    (δend εR εH rateParent ζ Ledit:ℝ) (hδ:0≤δend)
    (hR:εR≤δend/4) (hH:εH≤δend/4) (hRate:rateParent≤δend*ε/8)
    (hRate0:0≤rateParent) (hζ0:0≤ζ) (hζ:ζ≤rateParent)
    (hEdit:Ledit≤ζ*(markedVortexInnerVertices Q 0).card)
    (ζh ζe γ eCoeff:ℝ) (hζh:0<ζh) (hζe:0<ζe) (hγ:0<γ) (he:γ≤eCoeff):
    OrdinaryVortexAsymmetricPairingGeometryAt Q 0 Ncert ρ₀ δend εR εH Ledit ζh ζe γ eCoeff :=by
  have hI:((markedVortexInnerVertices Q 0).card:ℝ)≤Fintype.card (markedVortexVertexType Q 0):=by
    exact_mod_cast Finset.card_le_univ (markedVortexInnerVertices Q 0)
  have hEdit':Ledit≤ζ*Fintype.card (markedVortexVertexType Q 0):=
    hEdit.trans (mul_le_mul_of_nonneg_left hI hζ0)
  exact ordinary_vortex_asymmetric_pairing_from_vertex_rate Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hm 0 Q.length_pos
    Ncert N hN hsize hterminal δend εR εH rateParent ζ Ledit hδ hR hH hRate hRate0 hζ hEdit'
    ζh ζe γ eCoeff hζh hζe hγ he
end Oberwolfach
