module

public import Oberwolfach.OrdinaryTriangleRootFirstSafeSampleEvent
public import Oberwolfach.OrdinaryTriangleFreshFactorProbability
public import Oberwolfach.OrdinaryTriangleRootFirstConditionsFromParent

@[expose] public section
/-! A genuine mixed-factor parent supplies the fresh half of the
    root-first same-sample event and all its boundary class margins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_root_first_safe_sample_from_parent
    (γ κ b B:ℝ) (hγ:0<γ) (hκ:0<κ) (hb:0<b) (hB:0≤B):
    ∃ε ηf ζ:ℝ,0<ε ∧ 0<ηf ∧ 0<ζ ∧
    ∀(p:ℝ) (hp:0<p) (hp1:p≤1) (εsup:ℝ) (hsup:0<εsup) (q:ℕ),∃N:ℕ,
    ∀(V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (X T:Finset V) (Z W:Finset U)
      (data:MixedFreshParentDataInsideRoots γ κ b B ε ηf Qfactor F
        (ordinaryPhysicalGraph Qfactor Hfactor) (ordinaryPhysicalGraph F (fun _ _=>False))
        (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H Z X)
        (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl)
        (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr))
      (τ ν η ell βe βh a:ℝ)
      (D:OrdinaryRootCoverData Q F H X T Z W 3 (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U))),
    0≤τ→εsup≤p^2/4→τ+ν≤p^2/4→
    τ+ν+ell≤ζ*min (κ/2) γ*p/4→ν+η≤ζ*min (κ/2) γ*p/4→
    p≤4*ζ*min (κ/2) γ→20*Real.sqrt (2*p)≤ζ*min (κ/2) γ/2→
    2≤ζ*min (κ/2) γ*p*Fintype.card (V⊕U)/4→
    Disjoint Q F→(∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)→
    (∀u,3∣(Finset.univ.filter (fun v=>H v u)).card)→
    ordinaryPhysicalGraph Qfactor Hfactor≤spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)→
    let law:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-a≤law.probability (OrdinaryTriangleRootFirstSafeCleanupSample Q F H X T Z W
      (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U))
      (ν*Fintype.card (V⊕U)) D p βe βh)→
    1-a-(1/(Fintype.card V:ℝ)^q+1/(Fintype.card (V⊕U):ℝ)^q)≤law.probability (fun σ=>
      OrdinaryTriangleRootFirstSafeCleanupSample Q F H X T Z W
        (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U))
        (ν*Fintype.card (V⊕U)) D p βe βh σ ∧
      OrdinaryTriangleFreshFactorSample Q Qfactor F H Hfactor X Z p ζ εsup σ ∧
      OrdinaryProtectedHostCoverDownResult Q F H X T Z W 3
        ((ν+η+4*p)*Fintype.card (V⊕U)) ((ν+η+4*p)*Fintype.card (V⊕U))) :=by
  obtain ⟨ε,ηf,ζ,hε,hηf,hζ,hfresh⟩:=ordinary_triangle_fresh_factor_probability γ κ b B hγ hκ hb hB
  refine ⟨ε,ηf,ζ,hε,hηf,hζ,?_⟩
  intro p hp hp1 εsup hsup q
  obtain ⟨N,hN⟩:=hfresh p hp hp1 εsup hsup q
  refine ⟨N,?_⟩
  intro V U _ _ _ _ hn hu Q Qfactor F H Hfactor X T Z W data τ ν η ell βe βh a D
    hτ hεsup hsupport hclass hblock hpκ hsqrt horder hQF hbal hdiv hbase law hclean
  have hnum:=ordinary_triangle_root_first_conditions_from_parent Q Qfactor F H Hfactor X Z
    γ κ b B ε ηf p εsup τ ν η ell ζ hγ hκ hζ hp hp1 hτ hu data
    hεsup hsupport hclass hblock hpκ hsqrt horder
  have hf:=hN V U hn hu Q Qfactor F H Hfactor X Z data
  have hf':1-(1/(Fintype.card V:ℝ)^q+1/(Fintype.card (V⊕U):ℝ)^q)≤
      law.probability (OrdinaryTriangleFreshFactorSample Q Qfactor F H Hfactor X Z p ζ εsup):=by
    linarith only [hf]
  exact ordinary_triangle_root_first_safe_same_sample_event Q Qfactor F H Hfactor X T Z W
    p εsup τ ν η ell (min (κ/2) γ) ζ βe βh D hnum hQF hbal hdiv hbase law a
    (1/(Fintype.card V:ℝ)^q+1/(Fintype.card (V⊕U):ℝ)^q) hclean hf'
end Oberwolfach
