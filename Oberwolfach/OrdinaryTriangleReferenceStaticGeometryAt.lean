module

public import Oberwolfach.OrdinaryTriangleReferenceStaticGeometryAligned

@[expose] public section
/-! Name the uniform root-geometry callback so it can share its parameters
with the host event and fresh-factor probability selector. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleReferenceStaticGeometryAt
    (k:ℕ) (ρ₀ βH cParent Bparent pstar δ href εstar ηH gapRoot βout ξ ζ:ℝ) : Prop :=
    ∀pcap:ℝ,0<pcap→∃p:ℝ,0<p ∧ p≤1 ∧ p≤pcap ∧
    ∀η:ℝ,0<η→∃eps γ:ℝ,0<eps ∧ eps≤1 ∧ 0<γ ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [LinearOrder U],
    ∀(P:SimpleGraph V) (D vsize:ℕ) (β ε lam:ℝ)
      (Q:Vortex U P D β ε vsize) (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V)
      (hD:(Fintype.card V:ℝ)/2≤D) (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
      (hβ0:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hv:0<vsize)
      (hlam:0≤lam) (hlam1:lam≤1/4) (hlamρ:lam≤(ρ₀/8)/2) (hlamγ:lam≤γ/100)
      (hεξ:ε≤ξ/2) (hερ:ε≤ξ*(ρ₀/8)/2) (hεroot:2*ε^2≤lam)
      (i:ℕ) (hi:i<Q.length),
    let X:=markedVortexInnerVertices Q i;let T:=markedVortexDeeperVertices Q i;
    let Z:=markedVortexInnerHubs Q i;let W:=markedVortexDeeperHubs Q i;
    let A:=Finset.univ\T;let C:=Finset.univ\W;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X)
    let Zf:Finset C:=Finset.univ.filter (fun u=>u.val∈Z);
    ∀(G F:SimpleGraph (markedVortexVertexType Q i)) (H:markedVortexVertexType Q i→markedVortexHubType Q i→Prop)
      (ξroot κ ηbal:ℝ),0≤κ→κ≤γ/1000→0≤ηbal→ηbal*ε≤γ/8→
    OrdinaryNonrootWheelCoverResult 2 0 ξroot κ G F H X T Z W→
    let ell:=max (18*κ*Fintype.card (markedVortexVertexType Q i)+3*((W.card:ℝ)+T.card))
      (9*κ*Fintype.card (markedVortexVertexType Q i)+3*(T.card:ℝ));
    let bin:=ηbal*X.card;let f:ℝ:=T.card+2*W.card;let binner:=bin+3*ell+f;
    ∃Droot:OrdinaryRootCoverNonrootData G F H X T Z W 3 (10*ξroot*X.card) ell,
    (T.card:ℝ)+W.card≤lam*Fintype.card (markedVortexVertexType Q i) ∧
    0≤ell ∧ 0≤bin ∧ 0≤f ∧ 0≤binner ∧
    ∀p' eps':ℝ,0≤p'→p'≤p→eps'≤eps→
    OrdinaryNonrootGeometryStatic 3 k (ρ₀/16) (βH/4) βout (cParent*(1-2*δ)^2)
      (Bparent/((ρ₀/16)*pstar^(2*3-1))) (2*ηH+gapRoot) εstar η ξ ζ p' eps' f binner binner Xf Zf ∧
    ell+(p'+eps')*Fintype.card (A⊕C)≤ζ*Fintype.card A ∧
    ell+(p'+eps')*Fintype.card (A⊕C)≤ζ*Fintype.card C

theorem ordinary_triangle_reference_static_geometry_property
    (k:ℕ) (ρ₀ βH cParent Bparent pstar δ href εstar ηH gapRoot:ℝ)
    (hk:4≤k) (hρ₀:0<ρ₀) (hβH:0<βH) (hc:0<cParent) (hB:0≤Bparent) (hpstar:0<pstar)
    (hδ:0<δ) (hδsmall:δ<1/8) (hhref:0<href) (hηH:0<ηH) (hgapRoot:0<gapRoot)
    (hfit:2*ηH+gapRoot<εstar):
    ∃ξ ζ:ℝ,0<ξ ∧ 0<ζ ∧ ξ≤href/4 ∧ ζ≤href/4 ∧ ξ+ζ≤href/2 ∧
      OrdinaryTriangleReferenceStaticGeometryAt k ρ₀ βH cParent Bparent pstar δ href εstar ηH gapRoot (βH/8) ξ ζ :=by
  obtain ⟨βout,ξ,ζ,hβout,hβeq,hξ,hζ,hξcap,hζcap,hξζ,hmain⟩:=
    ordinary_triangle_reference_static_geometry_aligned k ρ₀ βH cParent Bparent pstar δ href εstar ηH gapRoot
      hk hρ₀ hβH hc hB hpstar hδ hδsmall hhref hηH hgapRoot hfit
  subst βout
  exact ⟨ξ,ζ,hξ,hζ,hξcap,hζcap,hξζ,hmain⟩
end Oberwolfach
