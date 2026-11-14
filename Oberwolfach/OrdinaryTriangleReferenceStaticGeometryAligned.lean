module

public import Oberwolfach.OrdinaryVortexTriangleRootCoverStaticGeometryOrderedMono
public import Oberwolfach.OrdinaryNonrootGeometryStaticSampleMono
public import Oberwolfach.OrdinaryVortexTriangleRootCoverStaticGeometryOrdered
public import Oberwolfach.OrdinaryVortexRootStaticGeometryOrderedChoice
public import Oberwolfach.OrdinaryTriangleRootCoverWithinBudget

@[expose] public section
/-! The actual triangle root cover satisfies all static nonroot geometry
and reserve-scale bounds when the preselected cover budget is respected. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_reference_static_geometry_aligned
    (k:ℕ) (ρ₀ βH cParent Bparent pstar δ href εstar ηH gapRoot:ℝ)
    (hk:4≤k) (hρ₀:0<ρ₀) (hβH:0<βH) (hc:0<cParent) (hB:0≤Bparent) (hpstar:0<pstar)
    (hδ:0<δ) (hδsmall:δ<1/8) (hhref:0<href) (hηH:0<ηH) (hgapRoot:0<gapRoot)
    (hfit:2*ηH+gapRoot<εstar):
    ∃βout ξ ζ:ℝ,0<βout ∧ βout=βH/8 ∧ 0<ξ ∧ 0<ζ ∧ ξ≤href/4 ∧ ζ≤href/4 ∧ ξ+ζ≤href/2 ∧
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
    ell+(p'+eps')*Fintype.card (A⊕C)≤ζ*Fintype.card C :=by
  have hbase:0<1-2*δ:=by linarith
  have hb:0<cParent*(1-2*δ)^2:=by positivity
  have hB':0≤Bparent/((ρ₀/16)*pstar^(2*3-1)):=by positivity
  have hgap:0<εstar-(2*ηH+gapRoot):=by linarith
  obtain ⟨βout,ξ,ζ,hβout,hβeq,hξ,hζ,hcapξ,hcapζ,hmain⟩:=
    ordinary_vortex_triangle_root_cover_static_geometry_ordered_mono 3 k ρ₀ (βH/4) (cParent*(1-2*δ)^2)
      (Bparent/((ρ₀/16)*pstar^(2*3-1))) (2*ηH+gapRoot) (εstar-(2*ηH+gapRoot)) (href/4)
      hk hρ₀ (by positivity) hb hB' hgap (by positivity)
  have hβeq':βout=βH/8:=by linarith
  have heps:(2*ηH+gapRoot)+(εstar-(2*ηH+gapRoot))=εstar:=by ring
  rw [heps] at hmain
  refine ⟨βout,ξ,ζ,hβout,hβeq',hξ,hζ,hcapξ,hcapζ,by linarith,?_⟩
  exact hmain
end Oberwolfach
