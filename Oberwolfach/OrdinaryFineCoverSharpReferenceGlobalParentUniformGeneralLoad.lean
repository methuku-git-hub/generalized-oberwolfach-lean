module

public import Oberwolfach.OrdinaryFineCoverSharpReferenceGeneralLoad
public import Oberwolfach.OrdinaryNonrootParentSmallRootsUniform

@[expose] public section
/-! A single host-uniform root-size scale restricts the original edited
parent, and the actual fine cover supplies its sharp reference on that host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fine_cover_sharp_reference_from_global_parent_uniform_general_load
    (m k loadK:ℕ) (hm:2≤m) (hk:4≤k) (α β₀ b₀ B h δ₀ ε₀ ω₀ gap:ℝ)
    (hβ:0<β₀) (hδ:0<δ₀) (hδ1:δ₀<1) (hω:0<ω₀) (hgap:0<gap)
    (hB:0≤B) (hb:0≤b₀) (hh:0≤h):
    ∃lam:ℝ,0<lam ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [LinearOrder U],
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop)
      (parent:OrdinaryEditedParentFields (m+1) (by omega) k α β₀ b₀ B h δ₀ ε₀ P Q F H)
      (X T:Finset V) (Z W:Finset U) (ξroot κ bin cin deep:ℝ)
      (hTX:T⊆X) (hWZ:W⊆Z) (hξ:0≤ξroot) (hκ:0≤κ) (hbin:0≤bin) (hdeep0:0≤deep)
      (hn:0<Fintype.card V) (hu0:0<Fintype.card U)
      (hu:Fintype.card U≤Fintype.card V) (hU:ω₀*Fintype.card V≤Fintype.card U)
      (hsize:(T.card:ℝ)+W.card≤lam*Fintype.card V)
      (hcover:OrdinaryFineWheelCoverResult m loadK ξroot κ Q F H X T Z W)
      (hgraph:Q≤P\F) (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
      (hdiv:∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)
      (hdeep:∀v∉T,|((Q.neighborFinset v∩T).card:ℝ)-2*(W.filter (H v)).card|≤deep)
      (hinner:∀v,|((spanningRestriction Q X).degree v:ℝ)-
        2*(Finset.univ.filter (fun u=>H v u∧v∈X∧u∈Z)).card|≤bin)
      (hcross:∀v∉X,|((Q.neighborFinset v∩X).card:ℝ)-2*(Z.filter (H v)).card|≤cin)
      (ω β εstar η ξ ζ p ε:ℝ),
    let ell:=max (18*κ*Fintype.card V+3*((W.card:ℝ)+((loadK:ℝ)+1)*T.card))
      (3*κ*Fintype.card V*((m:ℝ)+1)+(T.card:ℝ)*((m:ℝ)+1));
    let cover:=10*ξroot*X.card;let loss:=12*κ*Fintype.card V;
    let f:=deep+2*cover;let binner:=bin+deep+4*cover;let c:=cin+deep+loss;
    let A:=Finset.univ\T;let C:=Finset.univ\W;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X);
    let Zf:Finset C:=Finset.univ.filter (fun u=>u.val∈Z);
    OrdinaryNonrootGeometryStatic (m+1) k ω (β₀/2) β (b₀*(1-δ₀)^m) B (ε₀+gap)
      εstar η ξ ζ p ε f binner c Xf Zf→
    ell+(p+ε)*Fintype.card (A⊕C)≤ζ*Fintype.card A→
    ell+(p+ε)*Fintype.card (A⊕C)≤ζ*Fintype.card C→
    ∃D:OrdinaryRootCoverNonrootData Q F H X T Z W (m+1) cover ell,
      Nonempty (OrdinaryRootCoverSharpReferenceData P Q F H X T Z W (m+1) k (by omega) cover ell bin cin deep loss D
        α ω (β₀/2) β (b₀*(1-δ₀)^m) B h (δ₀/2) (ε₀+gap) εstar η ξ ζ p ε f binner c):=by
  obtain ⟨lam,hlam,hfields⟩:=ordinary_nonroot_parent_small_roots_uniform (m+1) (by omega) k hk α β₀ b₀ B h δ₀ ε₀ ω₀ gap
    hβ hδ hδ1 hω hgap hB hb hh
  refine ⟨lam,hlam,?_⟩
  intro V U _ _ _ _ P Q F H parent X T Z W ξroot κ bin cin deep hTX hWZ hξ hκ hbin hdeep0 hn hu0 hu hU hsize hcover hgraph hbal hdiv hdeep hinner hcross
    ω β εstar η ξ ζ p ε ell cover loss f binner c A C Xf Zf hstatic hscaleV hscaleU
  obtain ⟨fields⟩:=hfields V U P Q F H parent T W hn hu0 hu hU hsize
  have he:(m+1)-1=m:=by omega
  rw [he] at fields
  exact ordinary_fine_cover_sharp_reference_general_load m k loadK hm ξroot κ P Q F H X T Z W hTX hWZ hξ hκ bin cin deep hbin hdeep0 hcover hgraph hbal hdiv
    hdeep hinner hcross α ω (β₀/2) β (b₀*(1-δ₀)^m) B h (δ₀/2) (ε₀+gap) εstar η ξ ζ p ε fields hstatic hscaleV hscaleU
end Oberwolfach
