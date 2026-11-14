module

public import Oberwolfach.MarkedConstructedReferenceStateStep

@[expose] public section

/-! Fixed inputs for one step of marked cover-down. These are exactly the
explicit deterministic graph, profile, geometric and weight hypotheses of
that step, before any choice of the current bounded deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

structure MarkedReferenceLevelData
    (Gamma Color : Type) [Fintype Gamma] [Fintype Color]
    (r d N NI Kgeom : ℕ)
    (gamma rho omega t p0 betaA aLoA BA kappa ξ thetaDeep alphaInner omegaInner
     iota β aLo B η x omegaI hIcut deltaI etaBal : ℝ) where
  VP : Type
  UP : Type
  W : Type
  V : Type
  U : Type
  [inst7 : Fintype VP]
  [inst8 : Fintype UP]
  [inst9 : LinearOrder VP]
  [inst10 : DecidableEq UP]
  [inst11 : Fintype W]
  [inst12 : LinearOrder W]
  [inst13 : Fintype V]
  [inst14 : LinearOrder V]
  [inst15 : Fintype U]
  [inst16 : DecidableEq U]
  hnP : N≤ Fintype.card VP
  hUP : Fintype.card UP≤ Fintype.card VP
  hUPlow : omega*Fintype.card VP≤ (Fintype.card UP:ℝ)
  hnW : N≤ Fintype.card W
  hWlow : omegaInner*Fintype.card (V⊕U)≤ (Fintype.card W:ℝ)
  fA : V↪oVP
  gA : U↪UP
  PP : SimpleGraph VP
  πP : Equiv.Perm VP
  π : Equiv.Perm V
  hcomm : (∀ x,fA (π x)=πP (fA x))
  T : Finset VP
  Wrem : Finset UP
  hT : (∀ x,πP x∈T↔x∈T)
  hfX : Finset.univ.image fA=Finset.univ\T
  hgX : Finset.univ.image gA=Finset.univ\Wrem
  hTsize : (T.card:ℝ)≤ kappa*Fintype.card VP
  hWsize : (Wrem.card:ℝ)≤ kappa*Fintype.card VP
  hPdeg : (∀ x,(1/2+gamma/2)*Fintype.card VP≤ (PP.degree x:ℝ))
  hPreg : (∀ x,|(PP.degree x:ℝ)-2*Fintype.card UP/rho|≤ kappa*Fintype.card VP)
  qP : UP → Gamma → ℝ
  sP : UP → Color → ℝ
  aP : Gamma
  cP : Color
  hqP : (∀ u,qP u aP=t)
  hsP : (∀ u,sP u cP=(r+4:ℝ)*t)
  σBase : RawMarkedOutcome VP UP Gamma Color
  HBase : Bool → VP → UP → Prop
  I : Finset VP
  J : Finset UP
  hstats0 : let pRef:=rho*(r+4:ℝ)*t/2; let kRef:=pRef/(r+4:ℝ); let DRef:=2*Fintype.card UP/rho; MarkedReferenceStatistics PP πP d aP cP DRef (kappa/4) kappa (2*gamma) pRef kRef ((r+4:ℝ)*t) t σBase
  hcuts0 : let pRef:=rho*(r+4:ℝ)*t/2; let kRef:=pRef/(r+4:ℝ); MarkedReferenceCutFamilies PP πP d aP cP (2*gamma) pRef kRef t σBase
  hconfigsP0 : MarkedCommonConfigurationsWithSpokes r PP πP d betaA (kappa/4) σBase HBase
  hrowsP0 : let pRef:=rho*(r+4:ℝ)*t/2; let kRef:=pRef/(r+4:ℝ); MarkedRowsWithSpokes PP πP d (r+12) Finset.univ pRef kRef qP sP aP cP ((kappa/4)*Fintype.card VP) σBase HBase
  hindicesP0 : MarkedIndicesWithSpokes πP d (r+12) Finset.univ qP sP aP cP ((kappa/4)*Fintype.card VP) σBase HBase
  hrowOld0 : (∀ mark x,(∑ u,if ¬(rawMarkedPairSpokes πP d σBase aP cP mark x u↔HBase mark x u) then (1:ℝ) else 0)≤ (kappa/4)*Fintype.card UP)
  hcolOld0 : (∀ mark u,(∑ x,if ¬(rawMarkedPairSpokes πP d σBase aP cP mark x u↔HBase mark x u) then (1:ℝ) else 0)≤ (kappa/4)*Fintype.card VP)
  hDloP : let DRef:=2*Fintype.card UP/rho; (Fintype.card VP:ℝ)/2≤ DRef
  hDhiP : let DRef:=2*Fintype.card UP/rho; DRef≤ 2*Fintype.card VP
  tauRef : ℝ
  weightRef : (Fin (r+4+1) → VP) → ℝ
  hwRef : let DRef:=2*Fintype.card UP/rho; SuccessorSequenceWeightConditions PP πP (3*d) DRef tauRef aLoA BA weightRef
  hloadRef0 : let pRef:=rho*(r+4:ℝ)*t/2; let kRef:=pRef/(r+4:ℝ); let DRef:=2*Fintype.card UP/rho; (let seed:=fun C:MarkedWheel (Prod.fst:VP×VP → VP) Prod.snd Prod.fst Prod.snd (r+4) πP (3*d) (fun (_:VP) (_:UP)=>True) (fun _ _=>True)=>weightRef C.1.val/(DRef*pRef^(r+4)*kRef*((r+4:ℝ)*t)^(r+4)); ∀ root,rawMarkedWheelMarginal PP πP d pRef kRef qP sP aP cP root≠0 → |typedMarkedPotentialLoad seed (rawMarkedPairRims PP πP d σBase) HBase root-1|≤ kappa/4)
  hDeepConfigs0 : MarkedLocalConfigurationsWithSpokes r PP πP d Finset.univ (3*(min betaA (t/4))) (3*(min betaA (t/4))) σBase HBase
  hDeepLoad0 : let pRef:=rho*(r+4:ℝ)*t/2; let kRef:=pRef/(r+4:ℝ); let DRef:=2*Fintype.card UP/rho; MarkedLocalSpokeLoadsWithSpokes PP πP d (r+4) DRef pRef kRef ((r+4:ℝ)*t) weightRef (thetaDeep/4) σBase HBase
  xiDeep : ℝ
  hXi0 : 0≤ xiDeep
  hXiScale : (4*Kgeom+3*r+50:ℝ)*xiDeep≤ kappa/2
  hDeepGap : (1+2/rho)*xiDeep≤ t*omegaInner/32
  hTI : T⊆I
  hWremJ : Wrem⊆J
  hI : (∀ v,πP v∈I↔v∈I)
  hIsize : (I.card:ℝ)≤ ξ*Fintype.card VP
  hJsize : (J.card:ℝ)≤ ξ*Fintype.card VP
  hNI : NI≤ I.card
  hJlow : omegaI*I.card≤ J.card
  hJI : J.card≤ I.card
  hTcut : (T.card:ℝ)≤ hIcut*I.card
  hWcut : (Wrem.card:ℝ)≤ hIcut*J.card
  hTdeep : (T.card:ℝ)≤ xiDeep*Fintype.card VP
  hWdeep : (Wrem.card:ℝ)≤ xiDeep*Fintype.card VP
  f : W↪oV
  ρ : Equiv.Perm W
  hf : (∀ x,f (ρ x)=π (f x))
  D : ℝ
  τweight : ℝ
  hDlo : (Fintype.card W:ℝ)/2≤ D
  hDhi : D≤ 2*Fintype.card W
  weight : (Fin (r+4+1) → W) → ℝ
  hw : let P:=PP.comap fA; SuccessorSequenceWeightConditions (P.comap f) ρ (3*d) D τweight aLo B weight
  Zinner : Finset U
  hdtypesBase : (∀ u v,¬(HBase false v u∧ HBase true v u))
  hsepBase : (∀ u v z,HBase false v u → HBase true z u → v≠πP z)
  hXimage : let X:=Finset.univ.image f; X.image fA=I\T
  hZimage : Zinner.image gA=J\Wrem
  hLocalSize : iota*Fintype.card VP/4≤(Fintype.card W:ℝ)
  hrows00 : let pRef:=rho*(r+4:ℝ)*t/2; let kRef:=pRef/(r+4:ℝ); let pr:=pRef; let kr:=kRef; let Q:=fun u=>qP (gA u); let S:=fun u=>sP (gA u); let g:=aP; let c:=cP; MarkedRowsWithSpokes (PP.comap (f.comp fA)) ρ d 1 Finset.univ pr kr Q S g c ((t/8)*Fintype.card W) (rawMarkedRestrictPair (f.comp fA) gA σBase) (fun b x u=>HBase b (fA (f x)) (gA u))
  hconfigs00 : MarkedLocalConfigurationsWithSpokes r (PP.comap (f.comp fA)) ρ d Finset.univ (3*β) (3*β) (rawMarkedRestrictPair (f.comp fA) gA σBase) (fun b x u=>HBase b (fA (f x)) (gA u))
  hload00 : let pRef:=rho*(r+4:ℝ)*t/2; let kRef:=pRef/(r+4:ℝ); let pr:=pRef; let kr:=kRef; let sr:=(r+4:ℝ)*t; MarkedLocalSpokeLoadsWithSpokes (PP.comap (f.comp fA)) ρ d (r+4) D pr kr sr weight (η/4) (rawMarkedRestrictPair (f.comp fA) gA σBase) (fun b x u=>HBase b (fA (f x)) (gA u))
  errR0 : ℝ
  errI0 : ℝ
  heR0 : 0≤ errR0
  heI0 : 0≤ errI0
  hErrR0 : errR0≤ (x/2)*Fintype.card VP
  hErrI0 : errI0≤ (x/2)*Fintype.card VP
  hZlow : omegaInner*Fintype.card (V⊕U)≤ (Zinner.card:ℝ)
  hrowEnd00 : let pRef:=rho*(r+4:ℝ)*t/2; let kRef:=pRef/(r+4:ℝ); let pr:=pRef; let kr:=kRef; let g:=aP; let c:=cP; let X:=Finset.univ.image f; MarkedRowsWithSpokes PP πP d (r+12) (X.image fA) pr kr qP sP g c errR0 σBase HBase
  hidxEnd00 : let g:=aP; let c:=cP; MarkedIndicesWithSpokes πP d (r+12) (Zinner.image gA) qP sP g c errI0 σBase HBase
  errParent : ℝ
  heP : 0≤ errParent
  hNearP : (∀ v,|((PP.neighborFinset v∩I).card:ℝ)-2*J.card/rho|≤ errParent)
  hMinP : (∀ v,(1/2+2*alphaInner)*I.card≤ ((PP.neighborFinset v∩I).card:ℝ))
  hTinner : (T.card:ℝ)≤ alphaInner*I.card
  hErrParent : errParent≤ x*Fintype.card VP
  hinnerSize : let X:=Finset.univ.image f; ( (ordinaryInnerVertices X Zinner).card:ℝ)≤ ξ*Fintype.card V
  hX : let X:=Finset.univ.image f; (∀ x,π x∈X↔x∈X)
  hIotaSize : iota*Fintype.card VP≤ I.card
  hVhalf : (Fintype.card VP:ℝ)/2≤ Fintype.card V
  errInner : ℝ
  errDeep : ℝ
  heDeep : 0≤ errDeep
  hErrInner0 : errInner≤ (x/2)*Fintype.card VP
  hErrDeep0 : errDeep≤ (x/2)*Fintype.card VP
  hInnerBase : let EBase:=MarkedSampleArc PP πP (3*d) (fun e=>σBase (Sum.inl e)) false; let KBase:=MarkedSampleArc PP πP (3*d) (fun e=>σBase (Sum.inl e)) true; let SBase:=Finset.univ.filter (fun z:VP×UP=>HBase false z.1 z.2∨HBase true z.1 z.2); (∀ z,Sum.elim (fun v=>v∈I) (fun u=>u∈J) z → ∀ i, |markedFiniteDomainBalance (fun e:EBase=>e.val.1) (fun e=>e.val.2) (fun e:KBase=>e.val.1) (fun e=>e.val.2) (HBase true) Finset.univ SBase (r+4) I J z i|≤etaBal*I.card)
  hCutRBase : (∀ mark,BipartiteLargeCut (fun x:I=>fun y:I=>markedPhysicalRim PP πP (3*d) (fun e=>σBase (Sum.inl e)) mark x.val y.val) deltaI (2*hIcut))
  hCutSBase : (∀ mark,BipartiteLargeCut (relationMultiplicity (fun x:I=>fun u:J=>HBase mark x.val u.val)) deltaI (2*hIcut))
  hBalIBase : let EBase:=MarkedSampleArc PP πP (3*d) (fun e=>σBase (Sum.inl e)) false; let KBase:=MarkedSampleArc PP πP (3*d) (fun e=>σBase (Sum.inl e)) true; let SBase:=Finset.univ.filter (fun z:VP×UP=>HBase false z.1 z.2∨HBase true z.1 z.2); (∀ z i,|markedFiniteDomainBalance (fun e:EBase=>e.val.1) (fun e=>e.val.2) (fun e:KBase=>e.val.1) (fun e=>e.val.2) (HBase true) Finset.univ SBase (r+4) I J z i|≤ errInner)
  hBalTBase : let EBase:=MarkedSampleArc PP πP (3*d) (fun e=>σBase (Sum.inl e)) false; let KBase:=MarkedSampleArc PP πP (3*d) (fun e=>σBase (Sum.inl e)) true; let SBase:=Finset.univ.filter (fun z:VP×UP=>HBase false z.1 z.2∨HBase true z.1 z.2); (∀ z i,|markedFiniteDomainBalance (fun e:EBase=>e.val.1) (fun e=>e.val.2) (fun e:KBase=>e.val.1) (fun e=>e.val.2) (HBase true) Finset.univ SBase (r+4) T Wrem z i|≤ errDeep)

end Oberwolfach
