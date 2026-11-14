module

public import Oberwolfach.OrdinaryTriangleRootFreeUniformSharpCertificate
public import Oberwolfach.OrdinaryTriangleDeepIngredientsFromSampleLevel

@[expose] public section
/-! A root-free wheel certificate at an arbitrary level uses the actual
sample's row and endpoint tests and the sharp reference of that local host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 65536
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_root_free_sample_level_certificate
    (α ρ₀:ℝ) (k:ℕ) (hk:4≤k) (ω βout b Bweight hpack δref εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows:ℝ)
    (p βe βh ν cap εsup δsample τ:ℝ)
    (hfixed:OrdinaryTriangleRootFreeActualCoverAfterCleanup α k ω βout b Bweight hpack δref εstar cLinear κe pmin
      bHub BHub εf ηhub ηend ζfresh εrows p βe βh ν cap εsup δsample τ)
    (b₀:ℕ) (L:ℝ) (hL:0≤L) (eps:ℝ) (heps:0<eps):
    ∃M:ℕ,64≤M ∧
    ∀(n q D mv d:ℕ) (β ε:ℝ) (P:SimpleGraph (Fin n))
      (Vor:Vortex (Fin q) P D β ε mv) (π:Equiv.Perm (Fin n))
      (hπ:∀i x,π x∈Vor.extendedVertices i↔x∈Vor.extendedVertices i)
      (i:ℕ),i<Vor.length→
    ∀(pstar βP ηP ηH βH cParent Bparent εTri δParent href:ℝ)
      (pR pH κ aLoad εR εH bInner BInner ηInner capInner βeInner βhInner:ℝ)
      (density tR tH:ℕ→ℝ) (s:Fin q→Bool→ℝ) (j:Bool)
      (raw:RawWheelOutcome (Fin n) (Fin q) Bool Bool) (coins:Sym2 (Fin n)→Bool)
      (weightTri:OrdinaryCycle (P.comap (markedVortexVertexEmbedding Vor i)) 3→ℝ),
    OrdinaryTriangleSelectedSampleLevelData n q D mv k d β ε P Vor π hπ
      α ρ₀ pstar βP ηP ηH βH cParent Bparent εTri δParent href pR pH pmin κ aLoad εR εH
      bInner BInner ηInner capInner βeInner βhInner density tR tH s j raw coins i weightTri→
    ∀(G:SimpleGraph (markedVortexVertexType Vor i)) (H:markedVortexVertexType Vor i→markedVortexHubType Vor i→Prop)
      (weight:markedVortexVertexType Vor i→Sym2 (markedVortexVertexType Vor i⊕markedVortexHubType Vor i)→ℝ)
      (ξroot lam ellCap ηCap b₁ c₁ deep crossLoss βparent h εparent ξ ζ f binner c:ℝ)
      (dens Ledit βe₀ βh₀ δbal tP K γold κold bold Bold εold escale:ℝ),
    let Ploc:=P.comap (markedVortexVertexEmbedding Vor i);
    let Floc:=(permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Vor i);
    let I:=markedVortexInnerVertices Vor i;let T:=ordinaryVortexBufferedVertices Vor i 2;
    let B:=markedVortexInnerHubs Vor i;let W:=ordinaryVortexBufferedHubs Vor i 2;
    let perm:=markedVortexPermutation Vor π hπ i;
    let sloc:=fun u=>s (markedVortexHubEmbedding Vor i u);
    let rawloc:=ordinaryRawRestrictPair (markedVortexVertexEmbedding Vor i) (markedVortexHubEmbedding Vor i) raw;
    let cover:=10*ξroot*I.card;
    let ell:=max (18*aLoad*Fintype.card (markedVortexVertexType Vor i)+3*((W.card:ℝ)+T.card))
      (3*aLoad*Fintype.card (markedVortexVertexType Vor i)*3+(T.card:ℝ)*3);
    M≤I.card→0<Fintype.card (markedVortexVertexType Vor i)→
    (T.card:ℝ)+W.card≤lam*Fintype.card (markedVortexVertexType Vor i)→lam≤1/4→
    0≤ξroot→0≤aLoad→0≤lam→0≤ellCap→0≤ηCap→
    max (18*aLoad+3*lam) ((3*aLoad+lam)*3)≤ellCap→10*ξroot≤ηCap→
    OrdinaryRootCoverSharpReferenceExists Ploc G Floc H I T B W 3 k (by omega)
      cover ell b₁ c₁ deep crossLoss α ω βparent βout b Bweight h δref εparent εstar (cLinear*τ) ξ ζ p eps f binner c→
    hpack≤h-ξ-ζ→T⊆I→W⊆B→
    (T.card:ℝ)≤(βe/2)*Fintype.card (markedVortexVertexType Vor i⊕markedVortexHubType Vor i)→
    (W.card:ℝ)≤(βh/2)*Fintype.card (markedVortexVertexType Vor i⊕markedVortexHubType Vor i)→
    G≤Ploc\Floc→Disjoint G Floc→
    Fintype.card {v:markedVortexVertexType Vor i // v∉I}≤I.card^2→
    Fintype.card {u:markedVortexHubType Vor i // u∉B}≤I.card^2→
    OrdinaryDeepParentMargins Ploc Floc I B γold κold bold Bold εold ηend κe pmin pR pH dens
      (εR*I.card) (εH*B.card) L Ledit δbal εrows tP K escale→
    OrdinaryCleanupParentProfiles Ploc G Floc H perm d I B pR pH dens (εR*I.card) (εH*B.card)
      Ledit βe₀ βh₀ sloc j rawloc→
    EndpointPhysicalParentWeights Ploc I Iᶜ weight→
    EndpointPhysicalPotentialEvent Ploc Floc I B Iᶜ perm d j weight pR pH tP rawloc→
    OrdinaryMixedHubWeightsInnerScale 2 bHub BHub ηhub G Floc H I B→
    (∀v,Floc.degree v≤b₀)→L≤εf*I.card→
    (∀v,G.degree v=2*(Finset.univ.filter (H v)).card)→
    (∀u,3∣(Finset.univ.filter (fun v=>H v u)).card)→
    ∀κscale rate:ℝ,
    OrdinaryTriangleRootFirstScaledConditions G H I B p εsup τ ν ηCap (p*ellCap+δsample) κscale ζfresh→
    βe+3*max ηCap ellCap≤βe₀→βh+2*ellCap≤βh₀→ν+ηCap+4*p≤rate→
    OrdinaryWheelLikelySeparateCostsCertificate G Floc H I T B W 3
      (rate*Fintype.card (markedVortexVertexType Vor i⊕markedVortexHubType Vor i)) cover :=by
  obtain ⟨M,hM,hcover⟩:=ordinary_triangle_root_free_uniform_sharp_certificate α k hk ω βout b Bweight hpack δref εstar cLinear κe pmin
    bHub BHub εf ηhub ηend ζfresh εrows p βe βh ν cap εsup δsample τ hfixed b₀ L hL eps heps
  refine ⟨M,hM,?_⟩
  intro n q D mv d β ε P Vor π hπ i hi pstar βP ηP ηH βH cParent Bparent εTri δParent href
    pR pH κ aLoad εR εH bInner BInner ηInner capInner βeInner βhInner density tR tH s j raw coins weightTri hlevel
    G H weight ξroot lam ellCap ηCap b₁ c₁ deep crossLoss βparent h εparent ξ ζ f binner c
    dens Ledit βe₀ βh₀ δbal tP K γold κold bold Bold εold escale Ploc Floc I T B W perm sloc rawloc cover ell
    hsize hV hroot hlam4 hξroot ha hlam hellCap hηCap hell hη hrefsharp hpackcut hTX hWZ hT hW
    hhost hQF hJv hJu margins profile parent event hub hF hLf hbal hdiv κscale rate hscaled hbudgetE hbudgetH hfinish
  have hd:=ordinary_triangle_deep_ingredients_from_sample_level n q D mv k d β ε P Vor π hπ
    α ρ₀ pstar βP ηP ηH βH cParent Bparent εTri δParent href pR pH pmin κ aLoad εR εH
    bInner BInner ηInner capInner βeInner βhInner density tR tH s j raw coins i weightTri hi hlevel G H weight
    γold κold bold Bold εold ηend κe dens L Ledit βe₀ βh₀ δbal εrows tP K escale
    margins hhost profile parent event
  have hh:=hcover (markedVortexVertexType Vor i) (markedVortexHubType Vor i) Bool Bool
    Ploc G Floc H perm d I T B W ξroot aLoad lam ellCap ηCap b₁ c₁ deep crossLoss
    βparent h εparent ξ ζ f binner c pR pH dens (εR*I.card) (εH*B.card) tP Ledit βe₀ βh₀ δbal K γold κold bold Bold εold
    sloc j weight rawloc hsize hV hroot hlam4 hξroot ha hlam hellCap hηCap hell hη hrefsharp hpackcut hTX hWZ
    hT hW hQF
    (by convert hJv using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by convert hJu using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    (by convert hd using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by convert hub using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by intro v; convert hF v using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    hLf
    (by intro v; convert hbal v using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by intro u; convert hdiv u using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    κscale rate (by convert hscaled using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    hbudgetE hbudgetH hfinish
  convert hh using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
end Oberwolfach
