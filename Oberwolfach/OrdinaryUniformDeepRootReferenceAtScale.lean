module

public import Oberwolfach.OrdinaryDeepRootReferenceFromGlobalParentUniform

@[expose] public section
/-! Name the host-uniform root-reference consequence at its fixed scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryUniformDeepRootReferenceAtScale
    (r:ℕ) (hr:3≤r) (k:ℕ) (α β₀ b₀ B h δ₀ ε₀ ω₀ gap lam:ℝ):Prop :=
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U],
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop)
      (d:OrdinaryEditedParentFields r hr k α β₀ b₀ B h δ₀ ε₀ P Q F H)
      (X T:Finset V) (Z W:Finset U) (ηcover ell bin cin deep:ℝ)
      (D:OrdinaryRootCoverNonrootData Q F H X T Z W r ηcover ell)
      (ω β εstar η ξ ζ p ε f binner c:ℝ)
      (hn:0<Fintype.card V) (hu0:0<Fintype.card U)
      (hu:Fintype.card U≤Fintype.card V) (hU:ω₀*Fintype.card V≤Fintype.card U)
      (hsize:(T.card:ℝ)+W.card≤lam*Fintype.card V)
      (hell:0≤ell) (hgraph:Q≤P\F)
      (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
      (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
      (hTX:T⊆X) (hWZ:W⊆Z)
      (hdeep:∀v∉T,|((Q.neighborFinset v∩T).card:ℝ)-2*(W.filter (H v)).card|≤deep)
      (hinner:∀v,|((spanningRestriction Q X).degree v:ℝ)-
        2*(Finset.univ.filter (fun u=>H v u∧v∈X∧u∈Z)).card|≤bin)
      (hcross:∀v∉X,|((Q.neighborFinset v∩X).card:ℝ)-2*(Z.filter (H v)).card|≤cin)
      (hfull:deep+3*ell≤f)
      (hinnermargin:bin+3*ell+(deep+3*ell)≤binner)
      (hcrossmargin:cin+3*ell+(deep+3*ell)≤c),
    let A:=Finset.univ\T;let C:=Finset.univ\W;
    let Xf:Finset A:=Finset.univ.filter (fun v=>v.val∈X);
    let Zf:Finset C:=Finset.univ.filter (fun u=>u.val∈Z);
    OrdinaryNonrootGeometryStatic r k ω (β₀/2) β (b₀*(1-δ₀)^(r-1)) B (ε₀+gap)
      εstar η ξ ζ p ε f binner c Xf Zf→
    ell+(p+ε)*Fintype.card (A⊕C)≤ζ*Fintype.card A→
    ell+(p+ε)*Fintype.card (A⊕C)≤ζ*Fintype.card C→
    Nonempty (OrdinaryRootCoverDeepReferenceData P Q F H X T Z W r k hr ηcover ell bin cin deep D
      α ω (β₀/2) β (b₀*(1-δ₀)^(r-1)) B h (δ₀/2) (ε₀+gap) εstar η ξ ζ p ε f binner c)
end Oberwolfach
