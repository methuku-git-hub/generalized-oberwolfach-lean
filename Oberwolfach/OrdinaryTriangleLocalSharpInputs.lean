module

public import Oberwolfach.OrdinaryTriangleNumericSampleLevelCertificate

@[expose] public section
/-! Explicit local host data used by the initial and later triangle wheel
certificates.  The sharp reference is evidence about this host, not a wheel
certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleLocalSharpInputs
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder U]
    (P G F:SimpleGraph V) (H:V→U→Prop) (I T:Finset V) (B W:Finset U)
    (π:Equiv.Perm V) (d k:ℕ) (hk:3≤3) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (α ω βout b Bweight hpack δpack εstar cLinear p τ eps bHub BHub ηhub:ℝ)
    (pR pH density tR tH Ledit rateParent βeParent βhParent:ℝ)
    (ξroot aLoad ellCap cap βeGeo βhGeo:ℝ):Prop :=
    let cover:=10*ξroot*I.card;
    let ell:=max (18*aLoad*Fintype.card V+3*((W.card:ℝ)+T.card))
      (3*aLoad*Fintype.card V*3+(T.card:ℝ)*3);
    ∃lam b₁ c₁ deep crossLoss βparent h εparent ξ ζ f binner c:ℝ,
      Ledit≤rateParent*Fintype.card (V⊕U) ∧ G≤P\F ∧
      OrdinaryCleanupParentProfiles P G F H π d I B pR pH density tR tH Ledit βeParent βhParent s j raw ∧
      Nonempty (OrdinaryMixedHubWeightsInnerScale 2 bHub BHub ηhub G F H I B) ∧
      (∀v,G.degree v=2*(Finset.univ.filter (H v)).card) ∧
      (∀u,3∣(Finset.univ.filter (fun v=>H v u)).card) ∧
      (T.card:ℝ)+W.card≤lam*Fintype.card V ∧ lam≤1/4 ∧
      0≤ξroot ∧ 0≤aLoad ∧ 0≤lam ∧ 0≤ellCap ∧ 0≤cap ∧
      max (18*aLoad+3*lam) ((3*aLoad+lam)*3)≤ellCap ∧ 10*ξroot≤cap ∧
      OrdinaryRootCoverSharpReferenceExists P G F H I T B W 3 k hk
        cover ell b₁ c₁ deep crossLoss α ω βparent βout b Bweight h δpack εparent εstar (cLinear*τ) ξ ζ p eps f binner c ∧
      hpack≤h-ξ-ζ ∧
      (T.card:ℝ)≤(βeGeo/2)*Fintype.card (V⊕U) ∧
      (W.card:ℝ)≤(βhGeo/2)*Fintype.card (V⊕U)
end Oberwolfach
