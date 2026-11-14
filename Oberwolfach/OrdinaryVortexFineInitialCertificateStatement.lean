module

public import Oberwolfach.OrdinaryVortexFineCertificateAtGeneralLoad
public import Oberwolfach.OrdinaryProtectedTraceLocalWheelStructuralInputs

@[expose] public section
/-! Apply the selected local certificate to an actual protected history.
The graph avoidance, conflict degrees, balance and divisibility are derived
from that history and the common sampled reference. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryVortexFineInitialCertificateAt
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U]
    (s:OrdinaryVortexFineCertificateParametersGeneralLoad) (hcert:OrdinaryVortexFineCertificateAtGeneralLoad s)
    (P G:SimpleGraph V) (D mv:ℕ) (βv εv:ℝ)
    (Q:Vortex U P D βv εv mv) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (d:ℕ)
    (σ:RawWheelOutcome V U Γ Color) (Hs:V→U→Prop):Prop := by
  classical
  exact
    let f:=markedVortexVertexEmbedding Q 0;let g:=markedVortexHubEmbedding Q 0;
    letI : DecidableEq (markedVortexVertexType Q 0):=Classical.decEq _;
    letI : DecidableEq (markedVortexHubType Q 0):=Classical.decEq _;
    let I:=markedVortexInnerVertices Q 0;let T:=ordinaryVortexBufferedVertices Q 0 2;
    let B:=markedVortexInnerHubs Q 0;let W:=ordinaryVortexBufferedHubs Q 0 2;
    let Ploc:=P.comap f;let Gloc:=G.comap f;let Floc:=(permutationConflictGraph π (3*d)).comap f;
    let Hloc:=fun v u=>Hs (f v) (g u);let ρi:=markedVortexPermutation Q π hπ 0;
    let raw:=ordinaryRawRestrictPair f g σ;
    Disjoint G (permutationConflictGraph π (3*d)) →
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀u,(s.m+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    (2*(3*d):ℕ)≤s.b₀→(2*((3*d:ℕ):ℝ))≤s.L→
    ∀(ξroot aLoad lam bin cin deep crossLoss:ℝ),
    let n:ℝ:=Fintype.card (markedVortexVertexType Q 0⊕markedVortexHubType Q 0);
    let cover:=10*ξroot*I.card;
    let ell:=max (18*aLoad*Fintype.card (markedVortexVertexType Q 0)+3*((W.card:ℝ)+((s.loadK:ℝ)+1)*T.card))
      (3*aLoad*Fintype.card (markedVortexVertexType Q 0)*((s.m:ℝ)+1)+(T.card:ℝ)*((s.m:ℝ)+1));
    ∀(Root:OrdinaryRootCoverNonrootData Gloc Floc Hloc I T B W (s.m+1) cover ell)
      (βparent h εparent ξ ζ fout binner cross:ℝ)
      (pR pH density Ledit ρ₀ εR εH eParent hParent:ℝ)
      (sp:markedVortexHubType Q 0→Color→ℝ) (j:Color),
    s.hpack≤h-ξ-ζ→
    Nonempty (OrdinaryRootCoverSharpReferenceData Ploc Gloc Floc Hloc I T B W (s.m+1) s.k (by have hm := s.hm; omega)
      cover ell bin cin deep crossLoss Root s.α s.ω βparent s.β s.bRoot s.BRoot h s.δ εparent s.εstar s.ηpack ξ ζ s.p s.εgeom fout binner cross)→
    (T.card:ℝ)≤(s.βe/4)*n→(W.card:ℝ)≤(s.βh/2)*n→
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc ρi d I B pR pH density (εR*I.card) (εH*B.card)
      Ledit (eParent*εv) (hParent*εv) sp j raw→
    s.κ≤ρ₀/8→OrdinaryVortexAsymmetricPairingGeometryAt Q 0 s.Ncert ρ₀ s.δend εR εH Ledit s.ζhub s.ζlocal s.γ eParent→
    s.p₀≤pR→s.p₀≤pH→pH≤1→0≤εR→0≤εH→0≤Ledit→
    OrdinaryMixedHubWeightsInnerScale s.m s.bHub s.BHub s.ηhub Gloc Floc Hloc I B→
    ∀(Nfinish:ℕ) (rate θmatch ellCap finishCap kcap:ℝ),0<θmatch→
    θmatch≤(min (s.ζhub*s.γ*(1/4:ℝ)) (s.ζlocal*(1/4:ℝ))/2)*εv→
    s.εsup≤s.p^2/4→s.p≤4*θmatch→20*Real.sqrt (2*s.p)≤θmatch/2→
    0≤ξroot→0≤aLoad→0≤lam→lam≤1/4→
    max (max (max (4*s.n₀) (4*s.Nreserve)) (max s.Nclean 64)) (max s.Ncert Nfinish)≤I.card→
    (T.card:ℝ)+W.card≤lam*Fintype.card (markedVortexVertexType Q 0)→
    max (18*aLoad+3*(((s.loadK:ℝ)+1)*lam)) ((3*aLoad+lam)*((s.m:ℝ)+1))≤ellCap→10*ξroot≤finishCap→
    s.L≤kcap^2*n→
    OrdinaryAsymmetricFinishSchedule s.m Nfinish eParent hParent εv s.βe s.βh θmatch s.p s.δsample ellCap finishCap kcap rate s.ν s.cap→
    OrdinaryWheelLikelySeparateCostsCertificate Gloc Floc Hloc I T B W (s.m+1) (rate*n) cover 
end Oberwolfach
