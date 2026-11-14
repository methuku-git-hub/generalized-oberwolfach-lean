module

public import Oberwolfach.OrdinaryVortexBufferedGeneralRootCoverGeometryWithSlack

@[expose] public section
/-! Name the preselected vortex root-cover geometry callback so its scales
can be synchronized with the triangle packing theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryVortexBufferedGeneralRootGeometryWithSlackAtScale
    (mWheel k buffer:ℕ) (ρ₀ βparent b B εparent gap η βout ξ ζ p eps γ:ℝ):Prop :=
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [LinearOrder U],
    ∀(P:SimpleGraph V) (D vsize:ℕ) (β ε lam:ℝ)
      (Q:Vortex U P D β ε vsize) (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V)
      (hD:(Fintype.card V:ℝ)/2≤D) (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
      (hβ0:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hv:0<vsize)
      (hlam:0≤lam) (hlam1:lam≤1/4) (hlamρ:lam≤(ρ₀/8)/2) (hlamγ:lam≤γ/(1000*((mWheel:ℝ)+2)))
      (hεξ:ε≤ξ/2) (hερ:ε≤ξ*(ρ₀/8)/2) (hεroot:2*ε^buffer≤lam)
      (i:ℕ) (hi:i<Q.length),
    let X:=markedVortexInnerVertices Q i;let T:=ordinaryVortexBufferedVertices Q i buffer;
    let Z:=markedVortexInnerHubs Q i;let W:=ordinaryVortexBufferedHubs Q i buffer;
    let A:=Finset.univ\T;let C:=Finset.univ\W;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X)
    let Zf:Finset C:=Finset.univ.filter (fun u=>u.val∈Z);
    ∀(G F:SimpleGraph (markedVortexVertexType Q i)) (H:markedVortexVertexType Q i→markedVortexHubType Q i→Prop)
      (ξroot κ ηbal:ℝ),0≤κ→κ≤γ/(1000*((mWheel:ℝ)+2))→0≤ηbal→ηbal*ε≤γ/8→
    OrdinaryNonrootWheelCoverResult mWheel 0 ξroot κ G F H X T Z W→
    let ell:=max (18*κ*Fintype.card (markedVortexVertexType Q i)+3*((W.card:ℝ)+T.card))
      (3*κ*Fintype.card (markedVortexVertexType Q i)*((mWheel:ℝ)+1)+(T.card:ℝ)*((mWheel:ℝ)+1));
    let bin:=ηbal*X.card;let f:ℝ:=T.card+2*W.card+3*ell;let binner:=bin+3*ell+f;
    ∃Droot:OrdinaryRootCoverNonrootData G F H X T Z W (mWheel+1) (10*ξroot*X.card) ell,
    (T.card:ℝ)+W.card≤lam*Fintype.card (markedVortexVertexType Q i) ∧
    0≤ell ∧ 0≤bin ∧ 0≤f ∧ 0≤binner ∧
    OrdinaryNonrootGeometryStatic (mWheel+1) k (ρ₀/16) βparent βout b B εparent (εparent+gap) η ξ ζ p eps f binner binner Xf Zf ∧
    ell+(p+eps)*Fintype.card (A⊕C)≤ζ*Fintype.card A ∧
    ell+(p+eps)*Fintype.card (A⊕C)≤ζ*Fintype.card C
end Oberwolfach
