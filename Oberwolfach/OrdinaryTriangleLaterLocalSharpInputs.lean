module

public import Oberwolfach.OrdinaryTriangleLocalSharpInputs
public import Oberwolfach.OrdinaryTriangleLaterLocalBasics

@[expose] public section
/-! A protected later host, its sharp reference and cleanup profile give
the local input package used by the common-sample triangle certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_later_local_sharp_inputs
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder U]
    (P G F Gstart:SimpleGraph V) (H Hstart:V→U→Prop) (D mv:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε mv)
    (i:ℕ) (cost deepCost:ℕ→ℝ) (A:Finset (Sym2 V⊕(V×U)))
    (htrace:OrdinaryProtectedTrace Gstart Hstart (fun t=>Q.extendedVertices (t+1)) (fun t=>Q.extendedVertices (t+2))
      (fun t=>Q.extendedIndices (t+1)) (fun t=>Q.extendedIndices (t+2)) cost deepCost (i+1) A)
    (hstate:ordinaryHostResources G H=A)
    (hhost:G≤P\F) (hbal:∀v,G.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,3∣(Finset.univ.filter (fun v=>H v u)).card)
    (π:Equiv.Perm (markedVortexVertexType Q (i+1))) (d k:ℕ)
    (s:markedVortexHubType Q (i+1)→Color→ℝ) (j:Color)
    (raw:RawWheelOutcome (markedVortexVertexType Q (i+1)) (markedVortexHubType Q (i+1)) Γ Color)
    (α ω βout b Bweight hpack δpack εstar cLinear p τ eps bHub BHub ηhub:ℝ)
    (pR pH density tR tH Ledit rateParent βeParent βhParent:ℝ)
    (ξroot aLoad lam ellCap cap βeGeo βhGeo:ℝ)
    (b₁ c₁ deep crossLoss βparent h εparent ξ ζ f binner c:ℝ):
    let fv:=markedVortexVertexEmbedding Q (i+1);let gu:=markedVortexHubEmbedding Q (i+1);
    let Ploc:=P.comap fv;let Gloc:=G.comap fv;let Floc:=F.comap fv;let Hloc:=fun v u=>H (fv v) (gu u);
    let I:=markedVortexInnerVertices Q (i+1);let T:=ordinaryVortexBufferedVertices Q (i+1) 2;
    let B:=markedVortexInnerHubs Q (i+1);let W:=ordinaryVortexBufferedHubs Q (i+1) 2;
    let cover:=10*ξroot*I.card;
    let ell:=max (18*aLoad*Fintype.card (markedVortexVertexType Q (i+1))+3*((W.card:ℝ)+T.card))
      (3*aLoad*Fintype.card (markedVortexVertexType Q (i+1))*3+(T.card:ℝ)*3);
    0≤rateParent→Ledit≤rateParent*Fintype.card (markedVortexVertexType Q (i+1))→
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc π d I B pR pH density tR tH Ledit βeParent βhParent s j raw→
    Nonempty (OrdinaryMixedHubWeightsInnerScale 2 bHub BHub ηhub Gloc Floc Hloc I B)→
    (T.card:ℝ)+W.card≤lam*Fintype.card (markedVortexVertexType Q (i+1))→lam≤1/4→
    0≤ξroot→0≤aLoad→0≤lam→0≤ellCap→0≤cap→
    max (18*aLoad+3*lam) ((3*aLoad+lam)*3)≤ellCap→10*ξroot≤cap→
    OrdinaryRootCoverSharpReferenceExists Ploc Gloc Floc Hloc I T B W 3 k (by omega)
      cover ell b₁ c₁ deep crossLoss α ω βparent βout b Bweight h δpack εparent εstar (cLinear*τ) ξ ζ p eps f binner c→
    hpack≤h-ξ-ζ→0≤βeGeo→
    (T.card:ℝ)≤(βeGeo/4)*Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1))→
    (W.card:ℝ)≤(βhGeo/2)*Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1))→
    OrdinaryTriangleLocalSharpInputs Ploc Gloc Floc Hloc I T B W π d k (by omega) s j raw
      α ω βout b Bweight hpack δpack εstar cLinear p τ eps bHub BHub ηhub
      pR pH density tR tH Ledit rateParent βeParent βhParent ξroot aLoad ellCap cap βeGeo βhGeo :=by
  intro fv gu Ploc Gloc Floc Hloc I T B W cover ell hrate hL profile hub hroot hlam4
    hξroot ha hlam hellCap hcap hell hξcap hsharp hpackcut hβeGeo hT hW
  have hlocal:=ordinary_triangle_later_local_basics P G F Gstart H Hstart D mv β ε Q i cost deepCost A hhost htrace hstate hbal hdiv
  obtain ⟨hlocalHost,_,_,_,hlocalBal,hlocalDiv⟩:=hlocal
  have hVN:Fintype.card (markedVortexVertexType Q (i+1))≤Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1)):=
    Fintype.card_le_of_injective (Sum.inl:markedVortexVertexType Q (i+1)→markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1)) Sum.inl_injective
  have hLphysical:Ledit≤rateParent*Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1)):=by
    exact hL.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hVN) hrate)
  have hT':(T.card:ℝ)≤(βeGeo/2)*Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1)):=by
    have hN:(0:ℝ)≤Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1)):=by positivity
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
