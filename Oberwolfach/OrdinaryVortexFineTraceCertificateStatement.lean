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

def OrdinaryVortexFineCertificateFromProtectedTraceAt
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U]
    (s:OrdinaryVortexFineCertificateParametersGeneralLoad) (hcert:OrdinaryVortexFineCertificateAtGeneralLoad s)
    (P Gbase:SimpleGraph V) (Hbase:V→U→Prop) (D mv:ℕ) (βv εv:ℝ)
    (Q:Vortex U P D βv εv mv) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (d:ℕ)
    (σ:RawWheelOutcome V U Γ Color) (K:Finset (Sym2 V⊕(V×U)))
    (hr:∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,
      ((rawWheelGraph P σ)\permutationConflictGraph π (3*d)).Adj v w↔Gbase.Adj v w)
    (cost deepCost:ℕ→ℝ) (i:ℕ) (A:Finset (Sym2 V⊕(V×U)))
    (G:SimpleGraph V) (Hs:V→U→Prop):Prop := by
  classical
  exact
    let S:=Gbase\ordinaryResourceRim Gbase K;
    let H:=fun v u=>Hbase v u∧¬(Sum.inr (v,u)∈K);
    let X:=fun k=>Q.extendedVertices (k+1);let Tdeep:=fun k=>Q.extendedVertices (k+2);
    let Z:=fun k=>Q.extendedIndices (k+1);let Wdeep:=fun k=>Q.extendedIndices (k+2);
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1);
    letI : DecidableEq (markedVortexVertexType Q (i+1)):=Classical.decEq _;
    letI : DecidableEq (markedVortexHubType Q (i+1)):=Classical.decEq _;
    let I:=markedVortexInnerVertices Q (i+1);let T:=ordinaryVortexBufferedVertices Q (i+1) 2;
    let B:=markedVortexInnerHubs Q (i+1);let W:=ordinaryVortexBufferedHubs Q (i+1) 2;
    let Ploc:=P.comap f;let Gloc:=G.comap f;let Floc:=(permutationConflictGraph π (3*d)).comap f;
    let Hloc:=fun v u=>Hs (f v) (g u);let ρi:=markedVortexPermutation Q π hπ (i+1);
    let raw:=ordinaryRawRestrictPair f g σ;
    OrdinaryProtectedTrace S H X Tdeep Z Wdeep cost deepCost (i+1) A → ordinaryHostResources G Hs=A →
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀u,(s.m+1)∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    (2*(3*d):ℕ)≤s.b₀→(2*((3*d:ℕ):ℝ))≤s.L→
    ∀(ξroot aLoad lam bin cin deep crossLoss:ℝ),
    let n:ℝ:=Fintype.card (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1));
    let cover:=10*ξroot*I.card;
    let ell:=max (18*aLoad*Fintype.card (markedVortexVertexType Q (i+1))+3*((W.card:ℝ)+((s.loadK:ℝ)+1)*T.card))
      (3*aLoad*Fintype.card (markedVortexVertexType Q (i+1))*((s.m:ℝ)+1)+(T.card:ℝ)*((s.m:ℝ)+1));
    ∀(Root:OrdinaryRootCoverNonrootData Gloc Floc Hloc I T B W (s.m+1) cover ell)
      (βparent h εparent ξ ζ fout binner cross:ℝ)
      (pR pH density Ledit ρ₀ εR εH eParent hParent:ℝ)
      (sp:markedVortexHubType Q (i+1)→Color→ℝ) (j:Color),
    s.hpack≤h-ξ-ζ→
    Nonempty (OrdinaryRootCoverSharpReferenceData Ploc Gloc Floc Hloc I T B W (s.m+1) s.k (by have hm := s.hm; omega)
      cover ell bin cin deep crossLoss Root s.α s.ω βparent s.β s.bRoot s.BRoot h s.δ εparent s.εstar s.ηpack ξ ζ s.p s.εgeom fout binner cross)→
    (T.card:ℝ)≤(s.βe/4)*n→(W.card:ℝ)≤(s.βh/2)*n→
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc ρi d I B pR pH density (εR*I.card) (εH*B.card)
      Ledit (eParent*εv) (hParent*εv) sp j raw→
    s.κ≤ρ₀/8→OrdinaryVortexAsymmetricPairingGeometryAt Q (i+1) s.Ncert ρ₀ s.δend εR εH Ledit s.ζhub s.ζlocal s.γ eParent→
    s.p₀≤pR→s.p₀≤pH→pH≤1→0≤εR→0≤εH→0≤Ledit→
    OrdinaryMixedHubWeightsInnerScale s.m s.bHub s.BHub s.ηhub Gloc Floc Hloc I B→
    ∀(Nfinish:ℕ) (rate θmatch ellCap finishCap kcap:ℝ),0<θmatch→
    θmatch≤(min (s.ζhub*s.γ*(1/4:ℝ)) (s.ζlocal*(1/4:ℝ))/2)*εv→
    s.εsup≤s.p^2/4→s.p≤4*θmatch→20*Real.sqrt (2*s.p)≤θmatch/2→
    0≤ξroot→0≤aLoad→0≤lam→lam≤1/4→
    max (max (max (4*s.n₀) (4*s.Nreserve)) (max s.Nclean 64)) (max s.Ncert Nfinish)≤I.card→
    (T.card:ℝ)+W.card≤lam*Fintype.card (markedVortexVertexType Q (i+1))→
    max (18*aLoad+3*(((s.loadK:ℝ)+1)*lam)) ((3*aLoad+lam)*((s.m:ℝ)+1))≤ellCap→10*ξroot≤finishCap→
    s.L≤kcap^2*n→
    OrdinaryAsymmetricFinishSchedule s.m Nfinish eParent hParent εv s.βe s.βh θmatch s.p s.δsample ellCap finishCap kcap rate s.ν s.cap→
    OrdinaryWheelLikelySeparateCostsCertificate Gloc Floc Hloc I T B W (s.m+1) (rate*n) cover 
end Oberwolfach
