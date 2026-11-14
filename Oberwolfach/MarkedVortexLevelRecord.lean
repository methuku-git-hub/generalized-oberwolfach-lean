module

public import Oberwolfach.MarkedVortexGeometricRecordEvent
public import Oberwolfach.MarkedVortexParentRecordConsequences
public import Oberwolfach.MarkedReferenceLevelData
public import Oberwolfach.MarkedVortexRecordMapFields
public import Oberwolfach.MarkedVortexRetainedSpokeGeometry
public import Oberwolfach.MarkedVortexNestedActiveWeightTarget

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 60000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
theorem marked_vortex_level_record_from_bundles
    (r k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut:ℝ) (N NI Kgeom:ℕ)
    (hd:1≤d) (he:0≤ε)
    (hp:p=initialIndexDensity U D*s₀/2) (hk:kval=p/(((r+4):ℕ):ℝ))
    (hq0:∀u,q u a=s₀/(((r+4):ℕ):ℝ)) (hs0:∀u,s u j=s₀)
    (hXi0:0≤xiDeep) (hXiScale:(4*Kgeom+3*r+50:ℝ)*xiDeep≤κ/2)
    (hDeepGap:(1+2/initialIndexDensity U D)*xiDeep≤(s₀/(((r+4):ℕ):ℝ))*ω/32)
    (hParentWeight:∀i≤L,SuccessorSequenceWeightConditions (G.comap (markedVortexVertexEmbedding Q i))
      (markedVortexPermutation Q π hpres i) (3*d) (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity U D)
      τParent (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weightParent i))
    (hActiveWeight:∀i≤L+1,SuccessorSequenceWeightConditions (G.comap (markedVortexActiveVertexEmbedding Q i))
      (markedVortexActivePermutation Q π hpres i) (3*d)
      (2*((((Finset.univ\markedVortexInnerHubs Q i):Finset (markedVortexHubType Q i)).card):ℝ)/initialIndexDensity U D)
      τ (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weight i))
    (hGeo:MarkedVortexGeometricRecordEvent Q α ρ₀ κ hIcut ξ xiDeep ω x N NI L)
    (hRec:MarkedVortexParentRecordConsequences r (r+12) k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z βA βrec κ thetaDeep etaBal x eta deltaI hIcut)
    (i:ℕ) (hi:i≤L):
    Nonempty (MarkedReferenceLevelData Γ Color r d N NI Kgeom (α/16) (initialIndexDensity U D) (ρ₀/8)
      (s₀/(((r+4):ℕ):ℝ)) kstar βA (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4))
      κ ξ thetaDeep (α/8) ω (ε/4) βrec (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4))
      eta x (ρ₀/16) hIcut deltaI etaBal) := by
  dsimp only [MarkedVortexGeometricRecordEvent] at hGeo
  rcases hGeo with ⟨hGS,hGD,hGM,hGA⟩
  obtain ⟨hUP,hUPlow,hIsize,hJsize,hTsize,hWsize,hTcut,hWcut,hTinner,hTdeep,hWdeep,hVhalf,hWlow,hZlow,hinnerSize,hIotaSize,hLocalSize,hJlow,hJI⟩:=hGS i hi
  obtain ⟨hPdeg,hPreg,hDloP,hDhiP,hNearP,hMinP,heP,hErrParent⟩:=hGD i hi
  obtain ⟨hnP,hnW,hNI⟩:=hGM i hi
  obtain ⟨hDlo,hDhi⟩:=hGA i hi
  dsimp only [MarkedVortexParentRecordConsequences] at hRec
  rcases hRec with ⟨hRC,hRR,hRS,hRL,hRB,hRA,hRI,hRE⟩
  obtain ⟨hconfigsP0,hDeepConfigs0,hconfigs00⟩:=hRC i hi
  obtain ⟨hrowsP0,hindicesP0,hrowOld0,hcolOld0⟩:=hRR i hi
  obtain ⟨hstats0,hcuts0⟩:=hRS i hi
  obtain ⟨hDeepLoad0,hloadRef0⟩:=hRL i hi
  obtain ⟨errInner,errDeep,heDeep,hErrInner0,hErrDeep0,hBalIBase,hBalTBase,hInnerBase⟩:=hRB i hi
  obtain ⟨hrows00,hload00⟩:=hRA i hi
  obtain ⟨hCutRBase,hCutSBase⟩:=hRI i hi
  obtain ⟨errR0,errI0,heR0,heI0,hErrR0,hErrI0,hrowEnd00,hidxEnd00⟩:=hRE i hi
  obtain ⟨hcomm,hf,hI,hT,hX,hfX,hgX,hXimage,hZimage,hTI,hWremJ,hfcomp,hgcomp⟩:=marked_vortex_record_map_fields Q he π hpres i
  obtain ⟨hdtypesBase,hsepBase⟩:=marked_vortex_retained_spoke_geometry G D m d hd β ε Q π hpres a j z i
  have hwNested:=marked_vortex_nested_active_weight_target Q π hpres i d (r+4) (initialIndexDensity U D) τ
    (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weight (i+1)) (hActiveWeight (i+1) (by omega))
  have hc:(((r+4):ℕ):ℝ)≠0:=by positivity
  have hct:(((r+4):ℕ):ℝ)*(s₀/(((r+4):ℕ):ℝ))=s₀:=by field_simp
  have hpR:initialIndexDensity U D*(((r+4):ℕ):ℝ)*(s₀/(((r+4):ℕ):ℝ))/2=p:=by rw [hp];field_simp
  have hkR:(initialIndexDensity U D*(((r+4):ℕ):ℝ)*(s₀/(((r+4):ℕ):ℝ))/2)/(((r+4):ℕ):ℝ)=kval:=by rw [hpR,hk]
  have hctR:((r:ℝ)+4)*(s₀/(((r+4):ℕ):ℝ))=s₀:=by simpa only [Nat.cast_add,Nat.cast_ofNat] using hct
  have hpRR:initialIndexDensity U D*((r:ℝ)+4)*(s₀/(((r+4):ℕ):ℝ))/2=p:=by simpa only [Nat.cast_add,Nat.cast_ofNat] using hpR
  have hkRR:(initialIndexDensity U D*((r:ℝ)+4)*(s₀/(((r+4):ℕ):ℝ))/2)/((r:ℝ)+4)=kval:=by simpa only [Nat.cast_add,Nat.cast_ofNat] using hkR
  have hctN:((r:ℝ)+4)*(s₀/((r:ℝ)+4))=s₀:=by simpa only [Nat.cast_add,Nat.cast_ofNat] using hct
  have hpN:initialIndexDensity U D*((r:ℝ)+4)*(s₀/((r:ℝ)+4))/2=p:=by simpa only [Nat.cast_add,Nat.cast_ofNat] using hpR
  have hkN:(initialIndexDensity U D*((r:ℝ)+4)*(s₀/((r:ℝ)+4))/2)/((r:ℝ)+4)=kval:=by simpa only [Nat.cast_add,Nat.cast_ofNat] using hkR
  have hdecP:(Subtype.instDecidableEq:DecidableEq (markedVortexVertexType Q i))=(fun a b=>Classical.propDecidable (a=b)):=Subsingleton.elim _ _
  have hdecA:(Subtype.instDecidableEq:DecidableEq (markedVortexNonDeeperVertexType Q i))=(fun a b=>Classical.propDecidable (a=b)):=Subsingleton.elim _ _
  have hdecNext:(Subtype.instDecidableEq:DecidableEq (markedVortexVertexType Q (i+1)))=(fun a b=>Classical.propDecidable (a=b)):=Subsingleton.elim _ _
  try rw [hdecP] at hloadRef0
  try rw [hdecP] at hrowEnd00
  try rw [hdecP] at hfX
  try rw [hdecP] at hNearP
  try rw [hdecP] at hMinP
  try rw [hdecP] at hCutRBase
  try rw [hdecP] at hCutSBase
  try rw [hdecP] at hBalIBase
  try rw [hdecP] at hBalTBase
  try rw [hdecP] at hInnerBase
  try rw [hdecP] at hf
  try rw [hdecNext] at hf
  try rw [hdecA] at hXimage
  try rw [hdecA] at hinnerSize
  try rw [hdecA] at hX
  try rw [hdecA] at hrowEnd00
  try rw [hdecA] at hconfigs00
  try rw [hdecNext] at hconfigs00
  refine ⟨{
    VP := markedVortexVertexType Q i,
    UP := markedVortexHubType Q i,
    W := ↥((Finset.univ\markedVortexInnerVertices Q (i+1)):Finset (markedVortexVertexType Q (i+1))),
    V := markedVortexNonDeeperVertexType Q i,
    U := markedVortexNonDeeperHubType Q i,
    hnP := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hnP,
    hUP := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hUP,
    hUPlow := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hUPlow,
    hnW := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hnW,
    hWlow := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hWlow,
    fA := markedVortexNonDeeperVertexEmbedding Q i,
    gA := markedVortexNonDeeperHubToParent Q i,
    PP := G.comap (markedVortexVertexEmbedding Q i),
    πP := markedVortexPermutation Q π hpres i,
    π := markedVortexNonDeeperPermutation Q π hpres i,
    hcomm := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hcomm,
    T := markedVortexDeeperVertices Q i,
    Wrem := markedVortexDeeperHubs Q i,
    hT := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hT,
    hfX := by convert hfX using 1 <;> congr 2 <;> exact Subsingleton.elim _ _,
    hgX := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hgX,
    hTsize := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hTsize,
    hWsize := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hWsize,
    hPdeg := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hPdeg,
    hPreg := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hPreg,
    qP := fun u=>q (markedVortexHubEmbedding Q i u),
    sP := fun u=>s (markedVortexHubEmbedding Q i u),
    aP := a,
    cP := j,
    hqP := by intro u; exact hq0 (markedVortexHubEmbedding Q i u),
    hsP := by intro u; rw [hs0]; simpa only [Nat.cast_add, Nat.cast_ofNat] using hct.symm,
    σBase := rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) z.1,
    HBase := fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (markedVortexVertexEmbedding Q i x) (markedVortexHubEmbedding Q i u),
    I := markedVortexInnerVertices Q i,
    J := markedVortexInnerHubs Q i,
    hstats0 := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hstats0,
    hcuts0 := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hcuts0,
    hconfigsP0 := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hconfigsP0,
    hrowsP0 := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hrowsP0,
    hindicesP0 := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hindicesP0,
    hrowOld0 := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hrowOld0,
    hcolOld0 := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hcolOld0,
    hDloP := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hDloP,
    hDhiP := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hDhiP,
    tauRef := τParent,
    weightRef := weightParent i,
    hwRef := by simpa only using hParentWeight i hi,
    hloadRef0 := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hloadRef0,
    hDeepConfigs0 := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hDeepConfigs0,
    hDeepLoad0 := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hDeepLoad0,
    xiDeep := xiDeep,
    hXi0 := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hXi0,
    hXiScale := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hXiScale,
    hDeepGap := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hDeepGap,
    hTI := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hTI,
    hWremJ := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hWremJ,
    hI := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hI,
    hIsize := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hIsize,
    hJsize := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hJsize,
    hNI := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hNI,
    hJlow := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hJlow,
    hJI := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hJI,
    hTcut := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hTcut,
    hWcut := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hWcut,
    hTdeep := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hTdeep,
    hWdeep := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hWdeep,
    f := markedVortexNextActiveInNonDeeper Q i,
    ρ := markedVortexActivePermutation Q π hpres (i+1),
    hf := by intro v; have hh:=hf v; convert hh using 1 <;> congr 4 <;> exact Subsingleton.elim _ _,
    D := 2*((markedVortexInnerNonDeeperHubs Q i).card:ℝ)/initialIndexDensity U D,
    τweight := τ,
    hDlo := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hDlo,
    hDhi := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hDhi,
    weight := weight (i+1),
    hw := by simpa only using hwNested,
    Zinner := markedVortexInnerNonDeeperHubs Q i,
    hdtypesBase := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hdtypesBase,
    hsepBase := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hsepBase,
    hXimage := by convert hXimage using 1 <;> congr 3 <;> exact Subsingleton.elim _ _,
    hZimage := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hZimage,
    hLocalSize := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hLocalSize,
    hrows00 := by simp only [OrderEmbedding.coe_comp, Function.comp, Function.comp_apply, markedVortexNonDeeperHubToParent, Function.Embedding.coeFn_mk, Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] at hrows00 ⊢; convert hrows00 using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _,
    hconfigs00 := by simp only [OrderEmbedding.coe_comp, Function.comp, Function.comp_apply, markedVortexNonDeeperHubToParent, Function.Embedding.coeFn_mk, Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] at hconfigs00 ⊢; convert hconfigs00 using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _,
    hload00 := by simp only [OrderEmbedding.coe_comp, Function.comp, Function.comp_apply, markedVortexNonDeeperHubToParent, Function.Embedding.coeFn_mk, Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] at hload00 ⊢; convert hload00 using 1 <;> congr 6 <;> first | rfl | exact Subsingleton.elim _ _,
    errR0 := errR0,
    errI0 := errI0,
    heR0 := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using heR0,
    heI0 := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using heI0,
    hErrR0 := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hErrR0,
    hErrI0 := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hErrI0,
    hZlow := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hZlow,
    hrowEnd00 := by simp only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hp, hk] at hrowEnd00 ⊢; convert hrowEnd00 using 1 <;> congr 5 <;> exact Subsingleton.elim _ _,
    hidxEnd00 := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hidxEnd00,
    errParent := β*((markedVortexInnerVertices Q i).card:ℝ),
    heP := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using heP,
    hNearP := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hNearP,
    hMinP := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hMinP,
    hTinner := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hTinner,
    hErrParent := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hErrParent,
    hinnerSize := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hinnerSize,
    hX := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hX,
    hIotaSize := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hIotaSize,
    hVhalf := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hVhalf,
    errInner := errInner,
    errDeep := errDeep,
    heDeep := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using heDeep,
    hErrInner0 := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hErrInner0,
    hErrDeep0 := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hErrDeep0,
    hInnerBase := by dsimp only; intro v hv j; simpa only using hInnerBase v j,
    hCutRBase := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hCutRBase,
    hCutSBase := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hCutSBase,
    hBalIBase := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hBalIBase,
    hBalTBase := by simpa only [Nat.cast_add, Nat.cast_ofNat, hpN, hkN, hctN, hpRR, hkRR, hctR, hpR, hkR, hct, hp, hk, marked_vortex_active_hub_degree_target Q i (initialIndexDensity U D)] using hBalTBase
  }⟩
end Oberwolfach
