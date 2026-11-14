module

public import Oberwolfach.OrdinaryVortexFineCertificateAtGeneralLoad
public import Oberwolfach.OrdinaryVortexUniformEditCostEvents

@[expose] public section
/-! The actual all-edit sample event discharges the inner hub-weight input
of the packaged per-host fine-cover certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fine_certificate_from_uniform_weight_event_general_load
    (sCert:OrdinaryVortexFineCertificateParametersGeneralLoad) (hcert:OrdinaryVortexFineCertificateAtGeneralLoad sCert)
    (V₀ U₀:Type) [Fintype V₀] [Fintype U₀] [LinearOrder V₀] [LinearOrder U₀]
    (G₀:SimpleGraph V₀) (D₀ mv:ℕ) (βv εv:ℝ) (Vort:Vortex U₀ G₀ D₀ βv εv mv)
    (πglobal:Equiv.Perm V₀) (hπ:∀i x,πglobal x∈Vort.extendedVertices i↔x∈Vort.extendedVertices i)
    (i:ℕ) (hi:i<Vort.length) (d:ℕ)
    (Γ Color:Type) [Fintype Γ] [Fintype Color]
    (Q:SimpleGraph (markedVortexVertexType Vort i))
    (H:markedVortexVertexType Vort i → markedVortexHubType Vort i → Prop)
    (T:Finset (markedVortexVertexType Vort i)) (W:Finset (markedVortexHubType Vort i))
    (ξroot aLoad lam bin cin deep crossLoss:ℝ):
    let V:=markedVortexVertexType Vort i;let U:=markedVortexHubType Vort i;
    letI : DecidableEq V:=Classical.decEq _;letI : DecidableEq U:=Classical.decEq _;
    let X:=markedVortexInnerVertices Vort i;let Z:=markedVortexInnerHubs Vort i;
    let P:=G₀.comap (markedVortexVertexEmbedding Vort i);
    let F:=(permutationConflictGraph πglobal (3*d)).comap (markedVortexVertexEmbedding Vort i);
    let ρi:=markedVortexPermutation Vort πglobal hπ i;
    let n:ℝ:=Fintype.card (V⊕U);let cover:=10*ξroot*X.card;
    let ell:=max (18*aLoad*Fintype.card V+3*((W.card:ℝ)+((sCert.loadK:ℝ)+1)*T.card))
      (3*aLoad*Fintype.card V*((sCert.m:ℝ)+1)+(T.card:ℝ)*((sCert.m:ℝ)+1));
    ∀(D:OrdinaryRootCoverNonrootData Q F H X T Z W (sCert.m+1) cover ell)
      (βparent h εparent ξ ζ f binner cross:ℝ)
      (pR pH density Ledit capEdit ρ₀ εR εH eParent hParent:ℝ)
      (rates:U₀ → Color → ℝ) (j:Color) (rawGlobal:RawWheelOutcome V₀ U₀ Γ Color),
    let raw:=ordinaryRawRestrictPair (markedVortexVertexEmbedding Vort i) (markedVortexHubEmbedding Vort i) rawGlobal;
    sCert.hpack ≤ h-ξ-ζ  →  T⊆X  →  W⊆Z  → 
    Nonempty (OrdinaryRootCoverSharpReferenceData P Q F H X T Z W (sCert.m+1) sCert.k (by have:=sCert.hm;omega)
      cover ell bin cin deep crossLoss D sCert.α sCert.ω βparent sCert.β sCert.bRoot sCert.BRoot h sCert.δ εparent
      sCert.εstar sCert.ηpack ξ ζ sCert.p sCert.εgeom f binner cross)  → 
    (T.card:ℝ) ≤ (sCert.βe/4)*n  →  (W.card:ℝ) ≤ (sCert.βh/2)*n  → 
    Disjoint Q F  →  (∀v,(F.degree v:ℝ) ≤ sCert.L)  →  (∀v,F.degree v ≤ sCert.b₀)  → 
    OrdinaryCleanupParentProfiles P Q F H ρi d X Z pR pH density (εR*X.card) (εH*Z.card)
      Ledit (eParent*εv) (hParent*εv) (fun u=>rates (markedVortexHubEmbedding Vort i u)) j raw  → 
    sCert.κ ≤ ρ₀/8  →  OrdinaryVortexAsymmetricPairingGeometryAt Vort i sCert.Ncert ρ₀ sCert.δend εR εH Ledit
      sCert.ζhub sCert.ζlocal sCert.γ eParent  → 
    sCert.p₀ ≤ pR  →  sCert.p₀ ≤ pH  →  pH ≤ 1  →  0 ≤ εR  →  0 ≤ εH  →  0 ≤ Ledit  → 
    Q ≤ P  →  Ledit ≤ capEdit*X.card  → 
    OrdinaryUniformEditWeightEvents Vort πglobal hπ sCert.m d pR pH capEdit (eParent*εv) (hParent*εv)
      sCert.bHub sCert.BHub sCert.ηhub (fun _=>density)
      (fun k=>εR*(markedVortexInnerVertices Vort k).card) (fun k=>εH*(markedVortexInnerHubs Vort k).card)
      rates j rawGlobal  → 
    (∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)  → 
    (∀u,(sCert.m+1)∣(Finset.univ.filter (fun v=>H v u)).card)  → 
    ∀(Nfinish:ℕ) (rate θmatch ellCap finishCap kcap:ℝ),0<θmatch  → 
    θmatch ≤ (min (sCert.ζhub*sCert.γ*(1/4:ℝ)) (sCert.ζlocal*(1/4:ℝ))/2)*εv  → 
    sCert.εsup ≤ sCert.p^2/4  →  sCert.p ≤ 4*θmatch  →  20*Real.sqrt (2*sCert.p) ≤ θmatch/2  → 
    0 ≤ ξroot  →  0 ≤ aLoad  →  0 ≤ lam  →  lam ≤ 1/4  → 
    max (max (max (4*sCert.n₀) (4*sCert.Nreserve)) (max sCert.Nclean 64)) (max sCert.Ncert Nfinish) ≤ X.card  → 
    (T.card:ℝ)+W.card ≤ lam*Fintype.card V  → 
    max (18*aLoad+3*(((sCert.loadK:ℝ)+1)*lam)) ((3*aLoad+lam)*((sCert.m:ℝ)+1)) ≤ ellCap  →  10*ξroot ≤ finishCap  → 
    sCert.L ≤ kcap^2*n  → 
    OrdinaryAsymmetricFinishSchedule sCert.m Nfinish eParent hParent εv sCert.βe sCert.βh θmatch sCert.p
      sCert.δsample ellCap finishCap kcap rate sCert.ν sCert.cap  → 
    OrdinaryWheelLikelySeparateCostsCertificate Q F H X T Z W (sCert.m+1) (rate*n) cover :=by
  intro V U X Z P F ρi n cover ell D βparent h εparent ξ ζ f binner cross
    pR pH density Ledit capEdit ρ₀ εR εH eParent hParent rates j rawGlobal raw
    hpack hTX hWZ href hT hW hQF hF hFb profile hκ hgeo hpR hpH hpH1 hεR hεH hL hQP hLcap huniform
    hbalance hdiv Nfinish rate θmatch ellCap finishCap kcap hθ hθcap hεsup hpθ hsqrt hξroot haLoad hlam hlam1
    hsize hrootSize hell hcover hLcap' hfinish
  have hEvent:=huniform i hi Ledit hL hLcap
  obtain ⟨data⟩:=hEvent Q H
    (by convert profile using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by convert hQP using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  exact hcert V₀ U₀ G₀ D₀ mv βv εv Vort i Γ Color P Q F H ρi d T W ξroot aLoad lam bin cin deep crossLoss D
    βparent h εparent ξ ζ f binner cross pR pH density Ledit ρ₀ εR εH eParent hParent
    (fun u=>rates (markedVortexHubEmbedding Vort i u)) j raw hpack hTX hWZ href hT hW hQF hF hFb profile hκ hgeo
    hpR hpH hpH1 hεR hεH hL data hbalance hdiv Nfinish rate θmatch ellCap finishCap kcap hθ hθcap hεsup hpθ hsqrt
    hξroot haLoad hlam hlam1 hsize hrootSize hell hcover hLcap' hfinish
end Oberwolfach
