module

public import Oberwolfach.OrdinaryTrackedInitialReadyFromSharp
public import Oberwolfach.OrdinaryInitialCertificateFromLocalData

@[expose] public section
/-! For the actual tracked matching remainder, the corrected reservoir and
local same-sample certificate data feed the initial wheel certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryInitialCertificateFromLocalDataAt
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [LinearOrder U]
    (s:OrdinaryVortexFineCertificateParametersGeneralLoad) (hcert:OrdinaryVortexFineCertificateAtGeneralLoad s)
    (P G:SimpleGraph V) (D mv:ℕ) (βv εv:ℝ) (Q:Vortex U P D βv εv mv) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (d:ℕ)
    (σ:RawWheelOutcome V U Γ Color) (Hs:V→U→Prop)
    :Prop :=
    let f:=markedVortexVertexEmbedding Q 0;let g:=markedVortexHubEmbedding Q 0;
    letI : DecidableEq (markedVortexVertexType Q 0):=Classical.decEq _;
    letI : DecidableEq (markedVortexHubType Q 0):=Classical.decEq _;
    let I:=markedVortexInnerVertices Q 0;let T:=ordinaryVortexBufferedVertices Q 0 2;
    let B:=markedVortexInnerHubs Q 0;let W:=ordinaryVortexBufferedHubs Q 0 2;
    let Ploc:=P.comap f;let Gloc:=G.comap f;let Floc:=(permutationConflictGraph π (3*d)).comap f;
    let Hloc:=fun v u=>Hs (f v) (g u);let ρi:=markedVortexPermutation Q π hπ 0;
    let raw:=ordinaryRawRestrictPair f g σ;
    ∀(ξroot aLoad lam bin deep βparent h εparent ξ ζ pR pH density Ledit ρ₀ εR εH eParent hParent:ℝ)
      (sp:markedVortexHubType Q 0→Color→ℝ) (j:Color),
    let n:ℝ:=Fintype.card (markedVortexVertexType Q 0⊕markedVortexHubType Q 0);
    let cover:=10*ξroot*I.card;let loss:=12*aLoad*Fintype.card (markedVortexVertexType Q 0);
    let ell:=max (18*aLoad*Fintype.card (markedVortexVertexType Q 0)+3*((W.card:ℝ)+((s.loadK:ℝ)+1)*T.card))
      (3*aLoad*Fintype.card (markedVortexVertexType Q 0)*((s.m:ℝ)+1)+(T.card:ℝ)*((s.m:ℝ)+1));
    (2*(3*d):ℕ)≤s.b₀→(2*((3*d:ℕ):ℝ))≤s.L→s.hpack≤h-ξ-ζ→
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc ρi d I B pR pH density (εR*I.card) (εH*B.card)
      Ledit (eParent*εv) (hParent*εv) sp j raw→
    Nonempty (OrdinaryMixedHubWeightsInnerScale s.m s.bHub s.BHub s.ηhub Gloc Floc Hloc I B)→
    OrdinaryVortexAsymmetricPairingGeometryAt Q 0 s.Ncert ρ₀ s.δend εR εH Ledit s.ζhub s.ζlocal s.γ eParent→
    (T.card:ℝ)≤(s.βe/4)*n→(W.card:ℝ)≤(s.βh/2)*n→
    (T.card:ℝ)+W.card≤lam*Fintype.card (markedVortexVertexType Q 0)→
    (∃Root:OrdinaryRootCoverNonrootData Gloc Floc Hloc I T B W (s.m+1) cover ell,
      Nonempty (OrdinaryRootCoverSharpReferenceData Ploc Gloc Floc Hloc I T B W (s.m+1) s.k (by have hm:=s.hm;omega)
        cover ell bin bin deep loss Root s.α s.ω βparent s.β s.bRoot s.BRoot h s.δ εparent s.εstar s.ηpack ξ ζ s.p s.εgeom
        (deep+2*cover) (bin+deep+4*cover) (bin+deep+loss)))→
    s.κ≤ρ₀/8→s.p₀≤pR→s.p₀≤pH→pH≤1→0≤εR→0≤εH→0≤Ledit→
    ∀(Nfinish M:ℕ) (rate θmatch ellCap finishCap kcap:ℝ),0<θmatch→
    θmatch≤(min (s.ζhub*s.γ*(1/4:ℝ)) (s.ζlocal*(1/4:ℝ))/2)*εv→
    s.εsup≤s.p^2/4→s.p≤4*θmatch→20*Real.sqrt (2*s.p)≤θmatch/2→
    0≤ξroot→0≤aLoad→0≤lam→lam≤1/4→
    max (max (max (4*s.n₀) (4*s.Nreserve)) (max s.Nclean 64)) (max s.Ncert Nfinish)≤M→M≤I.card→
    max (18*aLoad+3*(((s.loadK:ℝ)+1)*lam)) ((3*aLoad+lam)*((s.m:ℝ)+1))≤ellCap→10*ξroot≤finishCap→
    s.L≤kcap^2*M→
    OrdinaryAsymmetricFinishSchedule s.m Nfinish eParent hParent εv s.βe s.βh θmatch s.p s.δsample ellCap finishCap kcap rate s.ν s.cap→
    OrdinaryWheelLikelySeparateCostsCertificate Gloc Floc Hloc I T B W (s.m+1) (rate*n) cover

theorem ordinary_tracked_initial_certificate_from_local_data {n q mAbs t aAbs bAbs:ℕ}
    (s:OrdinaryVortexFineCertificateParametersGeneralLoad) (hcert:OrdinaryVortexFineCertificateAtGeneralLoad s)
    (P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q→SimpleGraph (Fin n)) (hFs:∀u,(Fs u).IsRegularOfDegree 2)
    (C:∀u,Finset (Fs u).ConnectedComponent) (hsize:∀u (c:↥(C u)),Fintype.card c.val=s.m+1)
    (hS:S.IsRegularOfDegree (2*q)) (hSP:S≤P)
    (Inner Z Wterm A:Finset (Fin n)) (Hubs B Bterm:Finset (Fin q)) (ξ:ℝ)
    (K:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→Fin q→Prop)
    (cost:ℝ) (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (D mv:ℕ) (β ε:ℝ) (Vor:Vortex (Fin q) P D β ε mv)
    (hπ:∀i x,π x∈Vor.extendedVertices i↔x∈Vor.extendedVertices i):
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (σ e)
    let Bad:=permutationConflictGraph π (3*d)
    let Reference:=rawWheelGraph P raw\Bad
    let Href:=rawWheelSpokes π d raw false
    let Q:=S\ordinaryEmbeddedComplements Fs C f
    let H:=fun v u=>v∉Set.range (f u)
    let Gstart:=Q\ordinaryResourceRim Q K
    let Hstart:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K);
    OrdinaryCorrectedProtectedReservoirWitness (s.m+1) mAbs t aAbs bAbs ξ Reference Bad Href
      A Z Wterm Bterm B K JQ JH→
    OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs K cost f→
    OrdinaryInitialCertificateFromLocalDataAt s hcert P Gstart D mv β ε Vor π hπ d raw Hstart ∧
    let fv:markedVortexVertexType Vor 0↪Fin n:=(markedVortexVertexEmbedding Vor 0).toEmbedding
    let gu:=markedVortexHubEmbedding Vor 0;let ρ:=markedVortexPermutation Vor π hπ 0
    let rawLocal:=ordinaryRawRestrictPair fv gu raw;
    ∀w:markedVortexVertexType Vor 0⊕markedVortexHubType Vor 0,
      ((changed ((ordinaryPhysicalGraph (rawWheelGraph (P.comap fv) rawLocal)
        (rawWheelSpokes ρ d rawLocal false)).neighborFinset w)
        ((ordinaryPhysicalGraph (Gstart.comap fv) (fun v u=>Hstart (fv v) (gu u))).neighborFinset w)).card:ℝ)≤
        cost+2*((3*d:ℕ):ℝ) :=by
  intro raw Bad Reference Href Q H Gstart Hstart hw hf
  have h:=ordinary_tracked_initial_ready_from_sharp s hcert P S π d σ Fs hFs C hsize hS hSP
    Inner Z Wterm A Hubs B Bterm ξ K JQ JH cost f D mv β ε Vor hπ hw hf
  refine ⟨?_,h.2⟩
  exact ordinary_initial_certificate_from_local_data s hcert P Gstart D mv β ε Vor π hπ d raw Hstart h.1
end Oberwolfach
