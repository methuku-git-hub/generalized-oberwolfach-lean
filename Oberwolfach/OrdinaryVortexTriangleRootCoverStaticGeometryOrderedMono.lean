module

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

theorem ordinary_vortex_triangle_root_cover_static_geometry_ordered_mono
    (r k:ℕ) (ρ₀ βparent b B εparent gap cap:ℝ)
    (hk:4≤k) (hρ₀:0<ρ₀) (hβ:0<βparent) (hb:0<b) (hB:0≤B)
    (hgap:0<gap) (hcap:0<cap):
    ∃βout ξ ζ:ℝ,0<βout ∧ βout=βparent/2 ∧ 0<ξ ∧ 0<ζ ∧ ξ≤cap ∧ ζ≤cap ∧
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
    OrdinaryNonrootGeometryStatic r k (ρ₀/16) βparent βout b B εparent (εparent+gap) η ξ ζ p' eps' f binner binner Xf Zf ∧
    ell+(p'+eps')*Fintype.card (A⊕C)≤ζ*Fintype.card A ∧
    ell+(p'+eps')*Fintype.card (A⊕C)≤ζ*Fintype.card C :=by
  obtain ⟨βout,ξ,ζ,hβout,hβeq,hξ,hζ,hcapξ,hcapζ,hmain⟩:=
    ordinary_vortex_triangle_root_cover_static_geometry_ordered r k ρ₀ βparent b B εparent gap cap hk hρ₀ hβ hb hB hgap hcap
  refine ⟨βout,ξ,ζ,hβout,hβeq,hξ,hζ,hcapξ,hcapζ,?_⟩
  intro pcap hpcap
  obtain ⟨p,hp,hp1,hpc,hmain⟩:=hmain pcap hpcap
  refine ⟨p,hp,hp1,hpc,?_⟩
  intro η hη
  obtain ⟨eps,γ,heps,heps1,hγ,hmain⟩:=hmain η hη
  refine ⟨eps,γ,heps,heps1,hγ,?_⟩
  intro V U _ _ _ _ P D vsize β ε lam Q hreg hn hD hρlo hρhi hβ0 hβ1 hε hv hlam hlam1 hlamρ hlamγ hεξ hερ hεroot i hi
    X T Z W A C Xf Zf G F H ξroot κ ηbal hκ hκcap hηbal hbalcap hcover ell bin f binner
  obtain ⟨Droot,hroot,hell,hbin,hf,hbinner,hstatic,hreserveV,hreserveU⟩:=hmain V U P D vsize β ε lam Q hreg hn hD hρlo hρhi
    hβ0 hβ1 hε hv hlam hlam1 hlamρ hlamγ hεξ hερ hεroot i hi G F H ξroot κ ηbal hκ hκcap hηbal hbalcap hcover
  refine ⟨Droot,hroot,hell,hbin,hf,hbinner,?_⟩
  intro p' eps' hp' hpp heps
  have hstatic':=ordinary_nonroot_geometry_static_sample_mono r k (ρ₀/16) βparent βout b B εparent (εparent+gap)
    η ξ ζ p eps f binner binner p' eps' Xf Zf hstatic hp' hpp heps hbinner
  have hscale:(p'+eps')*Fintype.card (A⊕C)≤(p+eps)*Fintype.card (A⊕C):=
    mul_le_mul_of_nonneg_right (add_le_add hpp heps) (by positivity)
  exact ⟨hstatic',by linarith,by linarith⟩
end Oberwolfach
