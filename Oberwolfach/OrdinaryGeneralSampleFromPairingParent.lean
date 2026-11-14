module

public import Oberwolfach.OrdinaryGeneralFreshPairingProbabilityProperty
public import Oberwolfach.OrdinaryGeneralSameSampleProbability

@[expose] public section
/-! The actual pairing parent supplies the fresh half of the general-wheel
    same-sample probability, with its previously chosen tolerances. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 35000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_sample_from_pairing_parent
    (m b₀:ℕ) (hm:3≤m) (γ κ b B p₀ a εf ηf ζ:ℝ)
    (hfresh:OrdinaryGeneralFreshPairingProbabilityProperty m γ κ b B p₀ a εf ηf ζ)
    (p:ℝ) (hp:0<p) (hp1:p≤1) (ρ:ℝ) (hρ:0<ρ) (εsup:ℝ) (hsup:0<εsup) (q:ℕ):
    ∃N:ℕ,∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(P Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X T:Finset V) (Z W:Finset U) (η ell t ν:ℝ)
      (D:OrdinaryRootCoverData Q F H X T Z W (m+1) η ell)
      (tw:{v:V // v∉X}→ℝ)
      (data:MixedFreshPairingParentInsideRoots m b₀ γ κ b B p₀ a εf ηf Qfactor F
        (ordinaryPhysicalGraph Qfactor Hfactor) (ordinaryPhysicalGraph F (fun _ _=>False))
        (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H Z X)
        (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl)
        (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr) tw)
      (pR pH density tR tH Ledit βe₀ βh₀ βe βh budget loss:ℝ)
      (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color),
    0≤t→Disjoint Q F→(∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)→
    (∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)→
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Ledit βe₀ βh₀ s j raw→
    βe*Fintype.card (V⊕U)+3*max η ell≤βe₀*Fintype.card (V⊕U)→
    βh*Fintype.card (V⊕U)+2*ell≤βh₀*Fintype.card (V⊕U)→
    (∀σ (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W (m+1) η ell t ν D σ),
      BoundaryReserveSupportGood (ordinaryBoundaryGraph Q H X Z) p εsup σ→
      OrdinaryGeneralRootFirstMargins m Q Qfactor F H Hfactor X T Z W η ell t ν D σ O p ρ ζ εsup βe budget)→
    let law:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-loss≤law.probability (OrdinaryGeneralRootFirstCleanupSample m Q F H X T Z W η ell t ν D p βe βh)→
    1-loss-(1/(Fintype.card V:ℝ)^q+1/(Fintype.card (V⊕U):ℝ)^q)≤law.probability (fun σ=>
      OrdinaryGeneralRootFirstCleanupSample m Q F H X T Z W η ell t ν D p βe βh σ ∧
      OrdinaryGeneralFreshPairingSample m Q Qfactor F H Hfactor X Z p ρ ζ εsup σ ∧
      OrdinaryProtectedHostCoverDownResult Q F H X T Z W (m+1) budget budget) :=by
  obtain ⟨N,hN⟩:=hfresh b₀ p hp hp1 ρ hρ εsup hsup q
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hu P Q Qfactor F H Hfactor π d X T Z W η ell t ν D tw data
    pR pH density tR tH Ledit βe₀ βh₀ βe βh budget loss s j raw ht hQF hbal hdiv hprofile hmE hmH hnum law hclean
  have hf:=hN V U hn hu Q Qfactor F H Hfactor X Z tw data
  have hf':1-(1/(Fintype.card V:ℝ)^q+1/(Fintype.card (V⊕U):ℝ)^q)≤
      law.probability (OrdinaryGeneralFreshPairingSample m Q Qfactor F H Hfactor X Z p ρ ζ εsup):=by
    linarith only [hf]
  exact ordinary_general_same_sample_probability m hm P Q Qfactor F H Hfactor π d X T Z W η ell t ν D
    pR pH p density tR tH Ledit βe₀ βh₀ βe βh ρ ζ εsup budget s j raw ht hp.le hQF hbal hdiv hprofile hmE hmH hnum
    law loss (1/(Fintype.card V:ℝ)^q+1/(Fintype.card (V⊕U):ℝ)^q) hclean hf'
end Oberwolfach
