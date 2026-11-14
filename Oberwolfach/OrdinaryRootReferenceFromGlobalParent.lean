module

public import Oberwolfach.OrdinaryNonrootParentSmallRoots
public import Oberwolfach.OrdinaryRootCoverReferenceData

@[expose] public section
/-! One root-size scale supplies the complete restricted parent fields of the
selected root-cover reference; the remaining geometry stays explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_root_reference_from_global_parent
    (r:ℕ) (hr:3≤r) (k:ℕ) (hk:4≤k) (α β₀ b₀ B h δ₀ ε₀ ω₀ gap:ℝ)
    (hβ:0<β₀) (hδ:0<δ₀) (hδ1:δ₀<1) (hω:0<ω₀) (hgap:0<gap)
    (hB:0≤B) (hb:0≤b₀) (hh:0≤h):
    ∃lam:ℝ,0<lam ∧
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop)
      (d:OrdinaryEditedParentFields r hr k α β₀ b₀ B h δ₀ ε₀ P Q F H)
      (X T:Finset V) (Z W:Finset U) (ηcover ell bin cin:ℝ)
      (D:OrdinaryRootCoverNonrootData Q F H X T Z W r ηcover ell)
      (ω β εstar η ξ ζ p ε f binner c:ℝ)
      (hn:0<Fintype.card V) (hu0:0<Fintype.card U)
      (hu:Fintype.card U≤Fintype.card V) (hU:ω₀*Fintype.card V≤Fintype.card U)
      (hsize:(T.card:ℝ)+W.card≤lam*Fintype.card V)
      (hell:0≤ell) (hgraph:Q≤P\F)
      (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
      (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
      (hinner:∀v,|((spanningRestriction Q X).degree v:ℝ)-
        2*(Finset.univ.filter (fun u=>H v u∧v∈X∧u∈Z)).card|≤bin)
      (hcross:∀v∉X,|((Q.neighborFinset v∩X).card:ℝ)-2*(Z.filter (H v)).card|≤cin)
      (hfull:(T.card:ℝ)+2*W.card≤f)
      (hinnermargin:bin+3*ell+T.card+2*W.card≤binner)
      (hcrossmargin:cin+3*ell+T.card+2*W.card≤c),
    let A:=Finset.univ\T;let C:=Finset.univ\W;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X);
    let Zf:Finset C:=Finset.univ.filter (fun u=>u.val∈Z);
    OrdinaryNonrootGeometryStatic r k ω (β₀/2) β (b₀*(1-δ₀)^(r-1)) B (ε₀+gap)
      εstar η ξ ζ p ε f binner c Xf Zf→
    ell+(p+ε)*Fintype.card (A⊕C)≤ζ*Fintype.card A→
    ell+(p+ε)*Fintype.card (A⊕C)≤ζ*Fintype.card C→
    Nonempty (OrdinaryRootCoverReferenceData P Q F H X T Z W r k hr ηcover ell bin cin D
      α ω (β₀/2) β (b₀*(1-δ₀)^(r-1)) B h (δ₀/2) (ε₀+gap) εstar η ξ ζ p ε f binner c):=by
  obtain ⟨lam,hlam,hfields⟩:=ordinary_nonroot_parent_small_roots (V:=V) (U:=U) r hr k hk α β₀ b₀ B h δ₀ ε₀ ω₀ gap
    hβ hδ hδ1 hω hgap hB hb hh
  refine ⟨lam,hlam,?_⟩
  intro P Q F H d X T Z W ηcover ell bin cin D ω β εstar η ξ ζ p ε f binner c hn hu0 hu hU hsize
    hell hgraph hbal hdiv hinner hcross hfull hinnermargin hcrossmargin A C Xf Zf hstatic hscaleV hscaleU
  obtain ⟨hfield⟩:=hfields P Q F H d T W hn hu0 hu hU hsize
  exact ⟨⟨hell,hgraph,hbal,hdiv,hinner,hcross,hfull,hinnermargin,hcrossmargin,hfield,hstatic,hscaleV,hscaleU⟩⟩
end Oberwolfach
