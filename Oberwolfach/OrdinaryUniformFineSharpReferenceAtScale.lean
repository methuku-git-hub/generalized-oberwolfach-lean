module

public import Oberwolfach.OrdinaryFineCoverSharpReferenceGlobalParentUniform

@[expose] public section
/-! A host-uniform sharp-reference selector at its chosen root-size scale. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryUniformFineSharpReferenceAtScale
    (m k:ℕ) (hm:2≤m) (α β₀ b₀ B h δ₀ ε₀ ω₀ gap lam:ℝ):Prop :=
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [LinearOrder U],
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop)
      (parent:OrdinaryEditedParentFields (m+1) (by omega) k α β₀ b₀ B h δ₀ ε₀ P Q F H)
      (X T:Finset V) (Z W:Finset U) (ξroot κ bin cin deep:ℝ)
      (hTX:T⊆X) (hWZ:W⊆Z) (hξ:0≤ξroot) (hκ:0≤κ) (hbin:0≤bin) (hdeep0:0≤deep)
      (hn:0<Fintype.card V) (hu0:0<Fintype.card U)
      (hu:Fintype.card U≤Fintype.card V) (hU:ω₀*Fintype.card V≤Fintype.card U)
      (hsize:(T.card:ℝ)+W.card≤lam*Fintype.card V)
      (hcover:OrdinaryFineWheelCoverResult m 0 ξroot κ Q F H X T Z W)
      (hgraph:Q≤P\F) (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
      (hdiv:∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)
      (hdeep:∀v∉T,|((Q.neighborFinset v∩T).card:ℝ)-2*(W.filter (H v)).card|≤deep)
      (hinner:∀v,|((spanningRestriction Q X).degree v:ℝ)-
        2*(Finset.univ.filter (fun u=>H v u∧v∈X∧u∈Z)).card|≤bin)
      (hcross:∀v∉X,|((Q.neighborFinset v∩X).card:ℝ)-2*(Z.filter (H v)).card|≤cin)
      (ω β εstar η ξ ζ p ε:ℝ),
    let ell:=max (18*κ*Fintype.card V+3*((W.card:ℝ)+(((0:ℕ):ℝ)+1)*T.card))
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
        α ω (β₀/2) β (b₀*(1-δ₀)^m) B h (δ₀/2) (ε₀+gap) εstar η ξ ζ p ε f binner c)

theorem ordinary_uniform_fine_sharp_reference_at_scale_choice
    (m k:ℕ) (hm:2≤m) (hk:4≤k) (α β₀ b₀ B h δ₀ ε₀ ω₀ gap:ℝ)
    (hβ:0<β₀) (hδ:0<δ₀) (hδ1:δ₀<1) (hω:0<ω₀) (hgap:0<gap)
    (hB:0≤B) (hb:0≤b₀) (hh:0≤h):
    ∃lam:ℝ,0<lam ∧ OrdinaryUniformFineSharpReferenceAtScale m k hm α β₀ b₀ B h δ₀ ε₀ ω₀ gap lam :=by
  exact ordinary_fine_cover_sharp_reference_from_global_parent_uniform m k hm hk α β₀ b₀ B h δ₀ ε₀ ω₀ gap
    hβ hδ hδ1 hω hgap hB hb hh
end Oberwolfach
