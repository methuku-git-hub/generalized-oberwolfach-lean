module

public import Oberwolfach.OrdinaryVortexBufferedRootStaticGeometrySeparateChoice

@[expose] public section
/-! Name the already chosen separate edit and balance scales. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale
    (r k buffer:ℕ) (ρ₀ βparent b B εparent gap βout ξ ζ edit p η eps γ:ℝ):Prop :=
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U],
    ∀(P:SimpleGraph V) (D vsize:ℕ) (β ε lam:ℝ)
      (Q:Vortex U P D β ε vsize) (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V)
      (hD:(Fintype.card V:ℝ)/2≤D) (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
      (hβ0:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hv:0<vsize)
      (hlam:0≤lam) (hlam1:lam≤1/4) (hlamρ:lam≤(ρ₀/8)/2)
      (hεξ:ε≤ξ/2) (hερ:ε≤ξ*(ρ₀/8)/2) (hεroot:2*ε^buffer≤lam)
      (i:ℕ) (hi:i<Q.length),
    let X:=markedVortexInnerVertices Q i;let T:=ordinaryVortexBufferedVertices Q i buffer;
    let Z:=markedVortexInnerHubs Q i;let W:=ordinaryVortexBufferedHubs Q i buffer;
    let A:=Finset.univ\T;let C:=Finset.univ\W;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X)
    let Zf:Finset C:=Finset.univ.filter (fun u=>u.val∈Z);
    ∀f binner c ell:ℝ,0≤f→0≤binner→0≤c→0≤ell→
      f≤γ*Fintype.card A→binner≤γ*Fintype.card A→c≤γ*Fintype.card A→ell≤edit*Fintype.card A→
    (T.card:ℝ)+W.card≤lam*Fintype.card (markedVortexVertexType Q i) ∧
    OrdinaryNonrootGeometryStatic r k (ρ₀/16) βparent βout b B εparent (εparent+gap) η ξ ζ p eps f binner c Xf Zf ∧
    ell+(p+eps)*Fintype.card (A⊕C)≤ζ*Fintype.card A ∧
    ell+(p+eps)*Fintype.card (A⊕C)≤ζ*Fintype.card C 

theorem ordinary_vortex_buffered_root_static_geometry_separate_at_scale_choice
    (r k buffer:ℕ) (hbuffer:2≤buffer) (ρ₀ βparent b B εparent gap cap:ℝ)
    (hk:4≤k) (hρ₀:0<ρ₀) (hβ:0<βparent) (hb:0<b) (hB:0≤B)
    (hgap:0<gap) (hcap:0<cap):
    ∃βout ξ ζ edit:ℝ,0<βout ∧ βout=βparent/2 ∧ 0<ξ ∧ 0<ζ ∧ 0<edit ∧ ξ≤cap ∧ ζ≤cap ∧
    ∀pcap:ℝ,0<pcap→∃p:ℝ,0<p ∧ p≤1 ∧ p≤pcap ∧
    ∀η:ℝ,0<η→∃eps γ:ℝ,0<eps ∧ eps≤1 ∧ 0<γ ∧
      OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale r k buffer ρ₀ βparent b B εparent gap βout ξ ζ edit p η eps γ :=by
  exact ordinary_vortex_buffered_root_static_geometry_ordered_separate_choice r k buffer hbuffer ρ₀ βparent b B εparent gap cap
    hk hρ₀ hβ hb hB hgap hcap
end Oberwolfach
