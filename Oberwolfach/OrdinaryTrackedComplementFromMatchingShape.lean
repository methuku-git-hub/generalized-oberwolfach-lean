module

public import Oberwolfach.OrdinaryTrackedComplementOutcome
public import Oberwolfach.OrdinaryFixedTargetMatchingEmbeddingTrackedShape
public import Oberwolfach.OrdinaryMatchedComplementPhysicalEdit
public import Oberwolfach.OrdinarySameSampleUncoveredConflictReference
public import Oberwolfach.OrdinaryUsedSelectedReferenceFromOld
public import Oberwolfach.OrdinaryMatchedPackageOldReserve
public import Oberwolfach.OrdinarySampleLocalReferenceAvoidance
public import Oberwolfach.OrdinarySharedSamplePhysicalInclusion
public import Oberwolfach.OrdinaryMatchingProtectChoice

@[expose] public section
/-! Inputs for retaining the actual edited complement and its reference
comparison from the matching, protected placement and common sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTrackedComplementFromMatchingShape {n q K:ℕ}
    (Fs:Fin q→SimpleGraph (Fin n)) (hFs:∀u,(Fs u).IsRegularOfDegree 2)
    (C:∀u,Finset (Fs u).ConnectedComponent) (i₀:Fin K) (r m d:ℕ)
    (rsv θ lamMatch a γ δ:ℝ) (P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Inner:Finset (Fin n)) (Hubs:Finset (Fin q))
    (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))):Prop :=
  let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4}
  let Bad:=permutationConflictGraph π (3*d)
  let Reference:=rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e))\Bad
  let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false
  let Protect:=ordinaryMatchingProtect Reference Inner Kabs
  let Del:=ordinaryForbiddenSampleDeletion Sample S Reference Protect Bad Inner
  let G:=ordinaryForbiddenRequired S Sample Reference Bad Inner
  let J:=ordinaryEmptyRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false);
  0<n→0≤δ→S.IsRegularOfDegree (2*q)→
  (∀u (c:↥(C u)),Fintype.card c.val=r)→
  (∀u,((r:ℕ):ℝ)*(C u).card=rsv*n)→
  OrdinaryZeroRetentionEvent π d false σ→
  Kabs⊆ordinaryHostResources Reference Href→ ordinaryResourceRim Reference Kabs≤S→
  (∀v∈Inner,∀w∈Inner,S.Adj v w↔Sample.Adj v w)→
  OrdinarySelectedMatchingEmbeddingTrackedResult Fs hFs C i₀ rsv θ lamMatch a γ m d π P Del (S\Protect) G σ 0 J
    Inner Hubs (ordinaryReservoirSpokeLabels Kabs) δ→
  ∀(p k p₂ k₂ u t δDel κ edit e tcol:ℝ),
    0≤k→0≤k₂→0≤u→0≤t→0≤δDel→0≤κ→0≤edit→
    (max a γ)*n≤κ→
    (∀x,(Del.degree x:ℝ)≤δDel)→
    (∀v,((Finset.univ.filter (fun w=>Xor (S.Adj v w) (Sample.Adj v w))).card:ℝ)≤edit)→
    (∀c x,|(sampledColourDegree P (fun e=>(σ (Sum.inl e)).1) c x:ℝ)-
      markedExpandedPhysicalProbability p k p₂ k₂ u c*P.degree x|<t)→
    (∀v,|((Reference.degree v:ℝ)-2*((Finset.univ.filter (Href v)).card:ℝ))|≤e)→
    (∀w,|((Finset.univ.filter (fun v=>Href v w)).card:ℝ)-rsv*n|≤tcol)→
  let LF:ℝ:=2*((3*d:ℕ):ℝ)
  let newLoss:ℝ:=5*Real.sqrt δ*n
  let κref:ℝ:=κ+(2*k+2*k₂+u)*n+3*t+(6*d+4:ℕ)+δDel+LF
  let Lrim:ℝ:=edit+κref+newLoss
  let Lspoke:ℝ:=max (2*newLoss+(Lrim+e)/2) (2*(δ*n)+tcol);
  OrdinaryTrackedComplementOutcome P S π d σ Fs C Inner Hubs Kabs
    (Lrim+Lspoke+(ordinaryResourceRows Kabs).card+(ordinaryResourceHubs Kabs).card)
end Oberwolfach
