module

public import Oberwolfach.OrdinaryVortexAsymmetricPairingGeometry

@[expose] public section
/-! Named local geometry, so that a protected trace can retain all of its
pairing inputs together with the sharp reference on the same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D mv:ℕ} {β ε:ℝ}

def OrdinaryVortexAsymmetricPairingGeometryAt
    (Q:Vortex U G D β ε mv) (i Ncert:ℕ)
    (ρ₀ δend εR εH Ledit ζh ζe γ eCoeff:ℝ):Prop:=
  let A:=markedVortexInnerVertices Q i;let Z:=markedVortexInnerHubs Q i;
  let n:ℝ:=Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i);
  let κh:=γ*(1/4:ℝ)*ε;let κinner:=(1/4:ℝ)*ε;
  let c:=min (ζh*γ*(1/4:ℝ)) (ζe*(1/4:ℝ))/2;let θmatch:=c*ε;
  A.Nonempty ∧ Ncert≤A.card ∧ (ρ₀/8)*(A.card:ℝ)≤Z.card ∧ Z.card≤A.card ∧
  Fintype.card {u:markedVortexHubType Q i // u∉Z}≤A.card^2 ∧
  Fintype.card {v:markedVortexVertexType Q i // v∉A}≤(ordinaryPhysicalInnerDomain A Z).card^2 ∧
  εR*A.card+Ledit≤δend*A.card ∧ εH*Z.card+Ledit≤δend*A.card ∧
  0<κh ∧ 0<κinner ∧ 0<c ∧ 0<θmatch ∧
  κh*n≤γ*A.card ∧ κinner*n≤(ordinaryPhysicalInnerDomain A Z).card ∧
  θmatch≤ζh*κh ∧ θmatch≤ζe*κinner ∧ γ*A.card≤(eCoeff*ε)*n

theorem ordinary_vortex_asymmetric_pairing_geometry_at
    (Q:Vortex U G D β ε mv)
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:(Fintype.card V:ℝ)/2≤D)
    {ρ₀:ℝ} (hρ:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hm:0<mv) (i:ℕ) (hi:i<Q.length)
    (Ncert N:ℕ) (hN:Ncert≤N) (hsize:2/ε≤N) (hterminal:(N:ℝ)≤ε*mv/2)
    (δend εR εH rateParent Ledit:ℝ) (hδ:0≤δend)
    (hR:εR≤δend/4) (hH:εH≤δend/4) (hRate:rateParent≤δend*ε/8)
    (hEdit:Ledit≤rateParent*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i))
    (ζh ζe γ eCoeff:ℝ) (hζh:0<ζh) (hζe:0<ζe) (hγ:0<γ) (he:γ≤eCoeff):
    OrdinaryVortexAsymmetricPairingGeometryAt Q i Ncert ρ₀ δend εR εH Ledit ζh ζe γ eCoeff:=by
  exact ordinary_vortex_asymmetric_pairing_geometry Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hm i hi
    Ncert N hN hsize hterminal δend εR εH rateParent Ledit hδ hR hH hRate hEdit ζh ζe γ eCoeff hζh hζe hγ he
end Oberwolfach
