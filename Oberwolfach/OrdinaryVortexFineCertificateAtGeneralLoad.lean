module

public import Oberwolfach.OrdinaryVortexFineCoverCertificateFromScheduleGeneralLoad

@[expose] public section
/-! Package the concrete per-vortex callback so the numerical and probability
choices can be assembled without re-elaborating the full host statement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

structure OrdinaryVortexFineCertificateParametersGeneralLoad where
  m : ℕ
  k : ℕ
  loadK : ℕ
  b₀ : ℕ
  n₀ : ℕ
  Nclean : ℕ
  Nreserve : ℕ
  Ncert : ℕ
  hm : 3≤m
  α : ℝ
  ω : ℝ
  β : ℝ
  bRoot : ℝ
  BRoot : ℝ
  hpack : ℝ
  δ : ℝ
  εstar : ℝ
  ηpack : ℝ
  γ : ℝ
  bHub : ℝ
  BHub : ℝ
  p₀ : ℝ
  κ : ℝ
  ηhub : ℝ
  ζhub : ℝ
  ζlocal : ℝ
  δend : ℝ
  p : ℝ
  βe : ℝ
  βh : ℝ
  ν : ℝ
  cap : ℝ
  εsup : ℝ
  δsample : ℝ
  τ : ℝ
  L : ℝ
  εgeom : ℝ

def OrdinaryVortexFineCertificateAtGeneralLoad (s:OrdinaryVortexFineCertificateParametersGeneralLoad):Prop := by
  let m:=s.m
  let k:=s.k
  let loadK:=s.loadK
  let α:=s.α
  let ω:=s.ω
  let β:=s.β
  let bRoot:=s.bRoot
  let BRoot:=s.BRoot
  let hpack:=s.hpack
  let δ:=s.δ
  let εstar:=s.εstar
  let ηpack:=s.ηpack
  let γ:=s.γ
  let bHub:=s.bHub
  let BHub:=s.BHub
  let p₀:=s.p₀
  let κ:=s.κ
  let ηhub:=s.ηhub
  let ζhub:=s.ζhub
  let ζlocal:=s.ζlocal
  let δend:=s.δend
  let b₀:=s.b₀
  let p:=s.p
  let βe:=s.βe
  let βh:=s.βh
  let ν:=s.ν
  let cap:=s.cap
  let εsup:=s.εsup
  let δsample:=s.δsample
  let τ:=s.τ
  let L:=s.L
  let n₀:=s.n₀
  let Nclean:=s.Nclean
  let εgeom:=s.εgeom
  let Nreserve:=s.Nreserve
  let Ncert:=s.Ncert
  have hm:3≤m:=s.hm
  exact
    ∀(V₀ U₀:Type) [Fintype V₀] [Fintype U₀] [LinearOrder V₀] [LinearOrder U₀],
    ∀(G₀:SimpleGraph V₀) (D₀ mv:ℕ) (βv εv:ℝ) (Vort:Vortex U₀ G₀ D₀ βv εv mv) (i:ℕ),
    let V:=markedVortexVertexType Vort i;let U:=markedVortexHubType Vort i;
    letI : DecidableEq V:=Classical.decEq _;letI : DecidableEq U:=Classical.decEq _;
    let X:=markedVortexInnerVertices Vort i;let Z:=markedVortexInnerHubs Vort i;
    ∀(Γ Color:Type) [Fintype Γ] [Fintype Color],
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (T:Finset V) (W:Finset U) (ξroot aLoad lam bin cin deep crossLoss:ℝ),
    let n:ℝ:=Fintype.card (V⊕U);let cover:=10*ξroot*X.card;
    let ell:=max (18*aLoad*Fintype.card V+3*((W.card:ℝ)+((loadK:ℝ)+1)*T.card))
      (3*aLoad*Fintype.card V*((m:ℝ)+1)+(T.card:ℝ)*((m:ℝ)+1));
    ∀(D:OrdinaryRootCoverNonrootData Q F H X T Z W (m+1) cover ell)
      (βparent h εparent ξ ζ f binner cross:ℝ)
      (pR pH density Ledit ρ₀ εR εH eParent hParent:ℝ)
      (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color),
    hpack≤h-ξ-ζ→T⊆X→W⊆Z→
    Nonempty (OrdinaryRootCoverSharpReferenceData P Q F H X T Z W (m+1) k (by omega)
      cover ell bin cin deep crossLoss D α ω βparent β bRoot BRoot h δ εparent εstar ηpack ξ ζ p εgeom f binner cross)→
    (T.card:ℝ)≤(βe/4)*n→(W.card:ℝ)≤(βh/2)*n→
    Disjoint Q F→(∀v,(F.degree v:ℝ)≤L)→(∀v,F.degree v≤b₀)→
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density (εR*X.card) (εH*Z.card)
      Ledit (eParent*εv) (hParent*εv) s j raw→
    κ≤ρ₀/8→OrdinaryVortexAsymmetricPairingGeometryAt Vort i Ncert ρ₀ δend εR εH Ledit ζhub ζlocal γ eParent→
    p₀≤pR→p₀≤pH→pH≤1→0≤εR→0≤εH→0≤Ledit→
    OrdinaryMixedHubWeightsInnerScale m bHub BHub ηhub Q F H X Z→
    (∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)→
    (∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)→
    ∀(Nfinish:ℕ) (rate θmatch ellCap finishCap kcap:ℝ),0<θmatch→
    θmatch≤(min (ζhub*γ*(1/4:ℝ)) (ζlocal*(1/4:ℝ))/2)*εv→
    εsup≤p^2/4→p≤4*θmatch→20*Real.sqrt (2*p)≤θmatch/2→
    0≤ξroot→0≤aLoad→0≤lam→lam≤1/4→
    max (max (max (4*n₀) (4*Nreserve)) (max Nclean 64)) (max Ncert Nfinish)≤X.card→
    (T.card:ℝ)+W.card≤lam*Fintype.card V→
    max (18*aLoad+3*(((loadK:ℝ)+1)*lam)) ((3*aLoad+lam)*((m:ℝ)+1))≤ellCap→10*ξroot≤finishCap→
    L≤kcap^2*n→
    OrdinaryAsymmetricFinishSchedule m Nfinish eParent hParent εv βe βh θmatch p δsample ellCap finishCap kcap rate ν cap→
    OrdinaryWheelLikelySeparateCostsCertificate Q F H X T Z W (m+1) (rate*n) cover
end Oberwolfach
