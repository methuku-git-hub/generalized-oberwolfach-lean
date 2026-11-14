module

public import Oberwolfach.OrdinaryNonrootGeometryOrderedScaleChoice
public import Oberwolfach.OrdinaryVortexRootRestrictionGeometry

@[expose] public section
/-! Choose the fresh-reserve and nonroot margins before the host, and apply
them to the actual fixed-vortex root deletion at every nonterminal level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_root_static_geometry_ordered_choice
    (r k:ℕ) (ρ₀ βparent b B εparent gap cap:ℝ)
    (hk:4≤k) (hρ₀:0<ρ₀) (hβ:0<βparent) (hb:0<b) (hB:0≤B)
    (hgap:0<gap) (hcap:0<cap):
    ∃βout ξ ζ:ℝ,0<βout ∧ βout=βparent/2 ∧ 0<ξ ∧ 0<ζ ∧ ξ≤cap ∧ ζ≤cap ∧
    ∀pcap:ℝ,0<pcap→∃p:ℝ,0<p ∧ p≤1 ∧ p≤pcap ∧
    ∀η:ℝ,0<η→∃eps γ:ℝ,0<eps ∧ eps≤1 ∧ 0<γ ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U],
    ∀(P:SimpleGraph V) (D vsize:ℕ) (β ε lam:ℝ)
      (Q:Vortex U P D β ε vsize) (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V)
      (hD:(Fintype.card V:ℝ)/2≤D) (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
      (hβ0:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hv:0<vsize)
      (hlam:0≤lam) (hlam1:lam≤1/4) (hlamρ:lam≤(ρ₀/8)/2)
      (hεξ:ε≤ξ/2) (hερ:ε≤ξ*(ρ₀/8)/2) (hεroot:2*ε^2≤lam)
      (i:ℕ) (hi:i<Q.length),
    let X:=markedVortexInnerVertices Q i;let T:=markedVortexDeeperVertices Q i;
    let Z:=markedVortexInnerHubs Q i;let W:=markedVortexDeeperHubs Q i;
    let A:=Finset.univ\T;let C:=Finset.univ\W;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X)
    let Zf:Finset C:=Finset.univ.filter (fun u=>u.val∈Z);
    ∀f binner c ell:ℝ,0≤f→0≤binner→0≤c→0≤ell→
      f≤γ*Fintype.card A→binner≤γ*Fintype.card A→c≤γ*Fintype.card A→ell≤γ*Fintype.card A→
    (T.card:ℝ)+W.card≤lam*Fintype.card (markedVortexVertexType Q i) ∧
    OrdinaryNonrootGeometryStatic r k (ρ₀/16) βparent βout b B εparent (εparent+gap) η ξ ζ p eps f binner c Xf Zf ∧
    ell+(p+eps)*Fintype.card (A⊕C)≤ζ*Fintype.card A ∧
    ell+(p+eps)*Fintype.card (A⊕C)≤ζ*Fintype.card C :=by
  obtain ⟨βout,ξ,ζ,hβout,hβeq,hξ,hζ,hcapξ,hcapζ,hscale⟩:=
    ordinary_nonroot_geometry_ordered_scale_choice r k (ρ₀/16) βparent b B εparent gap cap
      hk (by positivity) hβ hb hB hgap hcap
  refine ⟨βout,ξ,ζ,hβout,hβeq,hξ,hζ,hcapξ,hcapζ,?_⟩
  intro pcap hpcap
  obtain ⟨p,hp,hp1,hpc,hscale⟩:=hscale pcap hpcap
  refine ⟨p,hp,hp1,hpc,?_⟩
  intro η hη
  obtain ⟨eps,γ,heps,heps1,hγ,hscale⟩:=hscale η hη
  refine ⟨eps,γ,heps,heps1,hγ,?_⟩
  intro V U _ _ _ _ P D vsize β ε lam Q hreg hn hD hρlo hρhi hβ0 hβ1 hε hv hlam hlam1 hlamρ hεξ hερ hεroot i hi
    X T Z W A C Xf Zf f binner c ell hf hbinner hc hell hf' hbinner' hc' hell'
  have hgeo:=ordinary_vortex_root_restriction_geometry P D vsize β ε ρ₀ lam ξ Q hreg hn hD hρ₀
    hρlo hρhi hβ0 hβ1 hε hv hξ.le hlam hlam1 hlamρ hεξ hερ hεroot i hi
  change (T.card:ℝ)+W.card≤lam*Fintype.card (markedVortexVertexType Q i) ∧
    0<Fintype.card A ∧ 0<Fintype.card C ∧
    ((ρ₀/8)/2)*Fintype.card A≤Fintype.card C ∧ Fintype.card C≤Fintype.card A ∧
    (Xf.card:ℝ)≤ξ*Fintype.card A ∧ (Zf.card:ℝ)≤ξ*Fintype.card A ∧
    (Zf.card:ℝ)≤ξ*Fintype.card C at hgeo
  obtain ⟨hroot,hA,hC,hratio,hupper,hX,hZ,hZC⟩:=hgeo
  have hratio':(ρ₀/16)*Fintype.card A≤Fintype.card C:=by nlinarith only [hratio]
  exact ⟨hroot,hscale A C Xf Zf f binner c ell hA hC hratio' hupper hX hZ hZC
    hf hbinner hc hell hf' hbinner' hc' hell'⟩
end Oberwolfach
