module

public import Oberwolfach.OrdinaryTriangleLocalSharpInputs
public import Oberwolfach.OrdinaryTriangleInitialLocalBasics

@[expose] public section
/-! The tracked initial host, its sharp reference and cleanup profile give
the local input package used by the common-sample triangle certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_initial_local_sharp_inputs
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder U]
    (P G F:SimpleGraph V) (H:V→U→Prop) (D mv:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε mv)
    (hhost:G≤P\F) (hbal:∀v,G.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,3∣(Finset.univ.filter (fun v=>H v u)).card)
    (π:Equiv.Perm (markedVortexVertexType Q 0)) (d k:ℕ)
    (s:markedVortexHubType Q 0→Color→ℝ) (j:Color)
    (raw:RawWheelOutcome (markedVortexVertexType Q 0) (markedVortexHubType Q 0) Γ Color)
    (α ω βout b Bweight hpack δpack εstar cLinear p τ eps bHub BHub ηhub:ℝ)
    (pR pH density tR tH Ledit ζcert rateParent βeParent βhParent:ℝ)
    (ξroot aLoad lam ellCap cap βeGeo βhGeo:ℝ)
    (b₁ c₁ deep crossLoss βparent h εparent ξ ζ f binner c:ℝ):
    let fv:=markedVortexVertexEmbedding Q 0;let gu:=markedVortexHubEmbedding Q 0;
    let Ploc:=P.comap fv;let Gloc:=G.comap fv;let Floc:=F.comap fv;let Hloc:=fun v u=>H (fv v) (gu u);
    let I:=markedVortexInnerVertices Q 0;let T:=ordinaryVortexBufferedVertices Q 0 2;
    let B:=markedVortexInnerHubs Q 0;let W:=ordinaryVortexBufferedHubs Q 0 2;
    let cover:=10*ξroot*I.card;
    let ell:=max (18*aLoad*Fintype.card (markedVortexVertexType Q 0)+3*((W.card:ℝ)+T.card))
      (3*aLoad*Fintype.card (markedVortexVertexType Q 0)*3+(T.card:ℝ)*3);
    0≤ζcert→ζcert≤rateParent→Ledit≤ζcert*I.card→
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc π d I B pR pH density tR tH Ledit βeParent βhParent s j raw→
    Nonempty (OrdinaryMixedHubWeightsInnerScale 2 bHub BHub ηhub Gloc Floc Hloc I B)→
    (T.card:ℝ)+W.card≤lam*Fintype.card (markedVortexVertexType Q 0)→lam≤1/4→
    0≤ξroot→0≤aLoad→0≤lam→0≤ellCap→0≤cap→
    max (18*aLoad+3*lam) ((3*aLoad+lam)*3)≤ellCap→10*ξroot≤cap→
    OrdinaryRootCoverSharpReferenceExists Ploc Gloc Floc Hloc I T B W 3 k (by omega)
      cover ell b₁ c₁ deep crossLoss α ω βparent βout b Bweight h δpack εparent εstar (cLinear*τ) ξ ζ p eps f binner c→
    hpack≤h-ξ-ζ→0≤βeGeo→
    (T.card:ℝ)≤(βeGeo/4)*Fintype.card (markedVortexVertexType Q 0⊕markedVortexHubType Q 0)→
    (W.card:ℝ)≤(βhGeo/2)*Fintype.card (markedVortexVertexType Q 0⊕markedVortexHubType Q 0)→
    OrdinaryTriangleLocalSharpInputs Ploc Gloc Floc Hloc I T B W π d k (by omega) s j raw
      α ω βout b Bweight hpack δpack εstar cLinear p τ eps bHub BHub ηhub
      pR pH density tR tH Ledit rateParent βeParent βhParent ξroot aLoad ellCap cap βeGeo βhGeo :=by
  intro fv gu Ploc Gloc Floc Hloc I T B W cover ell hζ hζrate hL profile hub hroot hlam4
    hξroot ha hlam hellCap hcap hell hξcap hsharp hpackcut hβeGeo hT hW
  have hlocal:=ordinary_triangle_initial_local_basics P G F H D mv β ε Q hhost hbal hdiv
  obtain ⟨hlocalHost,_,_,_,hlocalBal,hlocalDiv⟩:=hlocal
  have hI:I.card≤Fintype.card (markedVortexVertexType Q 0):=Finset.card_le_univ I
  have hVN:Fintype.card (markedVortexVertexType Q 0)≤Fintype.card (markedVortexVertexType Q 0⊕markedVortexHubType Q 0):=
    Fintype.card_le_of_injective (Sum.inl:markedVortexVertexType Q 0→markedVortexVertexType Q 0⊕markedVortexHubType Q 0) Sum.inl_injective
  have hrate:0≤rateParent:=hζ.trans hζrate
  have hLphysical:Ledit≤rateParent*Fintype.card (markedVortexVertexType Q 0⊕markedVortexHubType Q 0):=by
    have h1:=mul_le_mul_of_nonneg_right hζrate (show (0:ℝ)≤I.card by positivity)
    have h2:=mul_le_mul_of_nonneg_left (show (I.card:ℝ)≤Fintype.card (markedVortexVertexType Q 0⊕markedVortexHubType Q 0) by exact_mod_cast hI.trans hVN) hrate
    exact hL.trans (h1.trans h2)
  have hT':(T.card:ℝ)≤(βeGeo/2)*Fintype.card (markedVortexVertexType Q 0⊕markedVortexHubType Q 0):=by
    have hN:(0:ℝ)≤Fintype.card (markedVortexVertexType Q 0⊕markedVortexHubType Q 0):=by positivity
    nlinarith [mul_nonneg hβeGeo hN]
  dsimp only [OrdinaryTriangleLocalSharpInputs]
  refine ⟨lam,b₁,c₁,deep,crossLoss,βparent,h,εparent,ξ,ζ,f,binner,c,
    hLphysical,?_,?_,?_,?_,?_,hroot,hlam4,hξroot,ha,hlam,hellCap,hcap,hell,hξcap,?_,hpackcut,hT',hW⟩
  · convert hlocalHost using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  · convert profile using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  · convert hub using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  · intro v;convert hlocalBal v using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  · intro u;convert hlocalDiv u using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  · convert hsharp using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
end Oberwolfach
