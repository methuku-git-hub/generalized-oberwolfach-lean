module

public import Oberwolfach.MarkedVortexCorrectedRecordConsequences

@[expose] public section
/-! Numerical record fields at the initial level of a vortex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
def MarkedVortexZeroRecordConsequences
    (r h k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (σglobal:RawMarkedOutcome V U Γ Color) (Hglobal:Bool→V→U→Prop)
    (βA βrec κ thetaDeep etaBal x eta deltaI hIcut:ℝ):Prop:=
    let W:=fun i=>markedVortexVertexType Q i
    let Z:=fun i=>markedVortexHubType Q i
    let A:∀ i,Finset (W i):=fun i=>Finset.univ\markedVortexInnerVertices Q i
    let B:∀ i,Finset (Z i):=fun i=>Finset.univ\markedVortexInnerHubs Q i
    let X:=fun i=>↥(A i)
    let f:=fun i=>markedVortexActiveVertexEmbedding Q i
    let g:=fun i=>markedVortexActiveHubEmbedding Q i
    let ρ:=fun i=>markedVortexActivePermutation Q π hpres i
    let Dactive:=fun i=>2*((B i).card:ℝ)/initialIndexDensity U D
    let pstarLocal:=ρ₀*sstar/(2*((r+4:ℕ):ℝ))
    let fParent:=markedVortexVertexEmbedding Q
    let gParent:=markedVortexHubEmbedding Q
    let gWide:=markedVortexNonDeeperHubToPhysical Q
    let ρParent:=markedVortexPermutation Q π hpres
    let Dparent:=fun i=>2*(Fintype.card (Z i):ℝ)/initialIndexDensity U D;
    (∀ i≤L,i = 0 →
      let fP:=markedVortexVertexEmbedding Q i
      let gP:=markedVortexHubEmbedding Q i
      let fA:=markedVortexNonDeeperVertexEmbedding Q i
      let f:=markedVortexNextActiveInNonDeeper Q i
      let gA:markedVortexNonDeeperHubType Q i→markedVortexHubType Q i:=Subtype.val
      let ρP:=markedVortexPermutation Q π hpres i
      let ρ:=markedVortexActivePermutation Q π hpres (i+1)
      let σP:=rawMarkedRestrictPair fP gP σglobal
      let HP:=fun b x u=>Hglobal b (fP x) (gP u);
      MarkedCommonConfigurationsWithSpokes r (G.comap fP) ρP d βA (κ/4) σP HP ∧
      MarkedLocalConfigurationsWithSpokes r (G.comap fP) ρP d Finset.univ
        (3*(min βA ((s₀/((r+4:ℕ):ℝ))/4))) (3*(min βA ((s₀/((r+4:ℕ):ℝ))/4))) σP HP ∧
      MarkedLocalConfigurationsWithSpokes r ((G.comap fP).comap (fun x=>fA (f x))) ρ d Finset.univ
        (3*βrec) (3*βrec) (rawMarkedRestrictPair (fun x=>fA (f x)) gA σP)
        (fun b x u=>HP b (fA (f x)) (gA u))) ∧
    (∀ i≤L,i = 0 →
      let W:=markedVortexVertexType Q i; let Z:=markedVortexHubType Q i
      let f:=markedVortexVertexEmbedding Q i; let g:=markedVortexHubEmbedding Q i
      let ρ:=markedVortexPermutation Q π hpres i; let σ:=rawMarkedRestrictPair f g σglobal
      let H:=fun b x u=>Hglobal b (f x) (g u);
      MarkedRowsWithSpokes (G.comap f) ρ d (r+12) Finset.univ p kval (fun u=>q (g u)) (fun u=>s (g u)) a j ((κ/4)*Fintype.card W) σ H ∧
      MarkedIndicesWithSpokes ρ d (r+12) Finset.univ (fun u=>q (g u)) (fun u=>s (g u)) a j ((κ/4)*Fintype.card W) σ H ∧
      (∀ b x,(∑ u,if ¬(rawMarkedPairSpokes ρ d σ a j b x u↔H b x u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card Z) ∧
      (∀ b u,(∑ x,if ¬(rawMarkedPairSpokes ρ d σ a j b x u↔H b x u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card W)) ∧
    (∀ i≤L,i = 0 →
      let W:=markedVortexVertexType Q i
      let Z:=markedVortexHubType Q i
      let f:=markedVortexVertexEmbedding Q i
      let g:=markedVortexHubEmbedding Q i
      let ρ:=markedVortexPermutation Q π hpres i
      let rho:=initialIndexDensity U D
      let c:ℝ:=(r+4:ℕ)
      let t:=s₀/c
      let pRef:=rho*c*t/2
      let kRef:=pRef/c
      let DRef:=2*(Fintype.card Z:ℝ)/rho
      let σ:=rawMarkedRestrictPair f g σglobal;
      MarkedReferenceStatistics (G.comap f) ρ d a j DRef (κ/4) κ (2*(α/16)) pRef kRef (c*t) t σ ∧
      MarkedReferenceCutFamilies (G.comap f) ρ d a j (2*(α/16)) pRef kRef t σ) ∧
    (∀ i≤L,i = 0 →
      let W:=markedVortexVertexType Q i
      let Z:=markedVortexHubType Q i
      let P:=G.comap (markedVortexVertexEmbedding Q i)
      let ρ:=markedVortexPermutation Q π hpres i
      let Dload:=2*(Fintype.card Z:ℝ)/initialIndexDensity U D
      let σ:=rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σglobal
      let H:=fun b x u=>Hglobal b
        (markedVortexVertexEmbedding Q i x) (markedVortexHubEmbedding Q i u)
      let qi:=fun u=>q (markedVortexHubEmbedding Q i u)
      let si:=fun u=>s (markedVortexHubEmbedding Q i u);
      MarkedLocalSpokeLoadsWithSpokes P ρ d (r+4) Dload p kval s₀ (weightParent i) (thetaDeep/4) σ H ∧
      (let seed:=fun X:MarkedWheel (Prod.fst:W×W→W) Prod.snd Prod.fst Prod.snd (r+4) ρ (3*d)
          (fun (_:W) (_:Z)=>True) (fun _ _=>True)=>weightParent i X.1.val/(Dload*p^(r+4)*kval*s₀^(r+4));
        ∀ root:((W×W)⊕(W×W))⊕(Bool×W×Z),
          rawMarkedWheelMarginal P ρ d p kval qi si a j root≠0→
          |typedMarkedPotentialLoad seed (rawMarkedPairRims P ρ d σ) H root-1|≤κ/4)) ∧
    (∀ i≤L,i = 0 →
      let W:=markedVortexVertexType Q i
      let Z:=markedVortexHubType Q i
      let f:=markedVortexVertexEmbedding Q i
      let g:=markedVortexHubEmbedding Q i
      let ρ:=markedVortexPermutation Q π hpres i
      let σ:=rawMarkedRestrictPair f g σglobal
      let H:=fun b x u=>Hglobal b (f x) (g u)
      let E:=MarkedSampleArc (G.comap f) ρ (3*d) (fun e=>σ (Sum.inl e)) false
      let K:=MarkedSampleArc (G.comap f) ρ (3*d) (fun e=>σ (Sum.inl e)) true
      let S:=Finset.univ.filter (fun s:W×Z=>H false s.1 s.2∨H true s.1 s.2)
      let I:=markedVortexInnerVertices Q i
      let J:=markedVortexInnerHubs Q i
      let T:=markedVortexDeeperVertices Q i
      let R:=markedVortexDeeperHubs Q i
      let bal:=markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S (r+4);
      ∃ errInner errDeep:ℝ, 0≤errDeep ∧
      errInner≤(x/2)*Fintype.card W ∧ errDeep≤(x/2)*Fintype.card W ∧
      (∀ v j,|bal I J v j|≤errInner) ∧
      (∀ v j,|bal T R v j|≤errDeep) ∧
      (∀ v j,|bal I J v j|≤etaBal*I.card)) ∧
    (∀ i≤L,i = 0 →
      let Z:=markedVortexHubType Q i
      let Zkeep:=markedVortexNonDeeperHubType Q i
      let fP:=markedVortexVertexEmbedding Q i
      let gP:=markedVortexHubEmbedding Q i
      let fA:=markedVortexNonDeeperVertexEmbedding Q i
      let f:=markedVortexNextActiveInNonDeeper Q i
      let gA:Zkeep→Z:=Subtype.val
      let ρ:=markedVortexActivePermutation Q π hpres (i+1)
      let σP:=rawMarkedRestrictPair fP gP σglobal
      let HP:=fun b x u=>Hglobal b (fP x) (gP u);
      MarkedRowsWithSpokes ((G.comap fP).comap (fun x=>fA (f x))) ρ d 1 Finset.univ p kval
        (fun u=>q (gP (gA u))) (fun u=>s (gP (gA u))) a j
        (((s₀/((r+4:ℕ):ℝ))/8)*Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q (i+1)):Finset (markedVortexVertexType Q (i+1))))
        (rawMarkedRestrictPair (fun x=>fA (f x)) gA σP) (fun b x u=>HP b (fA (f x)) (gA u)) ∧
      MarkedLocalSpokeLoadsWithSpokes ((G.comap fP).comap (fun x=>fA (f x))) ρ d (r+4) (Dactive (i+1)) p kval s₀ (weight (i+1)) (eta/4)
        (rawMarkedRestrictPair (fun x=>fA (f x)) gA σP) (fun b x u=>HP b (fA (f x)) (gA u))) ∧
    (∀ i≤L,i = 0 →
    (∀ mark,BipartiteLargeCut
      (fun x:↥(markedVortexInnerVertices Q i)=>fun y:↥(markedVortexInnerVertices Q i)=>
        markedPhysicalRim (G.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hpres i) (3*d)
          (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σglobal (Sum.inl e)) mark x.val y.val) deltaI (2*hIcut)) ∧
    (∀ mark,BipartiteLargeCut (relationMultiplicity (fun x:↥(markedVortexInnerVertices Q i)=>fun u:↥(markedVortexInnerHubs Q i)=>
      Hglobal mark
        (markedVortexVertexEmbedding Q i x.val) (markedVortexHubEmbedding Q i u.val))) deltaI (2*hIcut))) ∧
    ∀ i≤L,i = 0 →
      let W:=markedVortexVertexType Q i
      let Z:=markedVortexHubType Q i
      let fP:=markedVortexVertexEmbedding Q i
      let gP:=markedVortexHubEmbedding Q i
      let ρ:=markedVortexPermutation Q π hpres i
      let fA:=markedVortexNonDeeperVertexEmbedding Q i
      let f:=markedVortexNextActiveInNonDeeper Q i
      let gA:=markedVortexNonDeeperHubToParent Q i
      let X:=Finset.univ.image f
      let Zinner:=markedVortexInnerNonDeeperHubs Q i
      let ω:=rawMarkedRestrictPair fP gP σglobal
      let H:=fun b x u=>Hglobal b (fP x) (gP u);
      ∃ errR errI:ℝ,0≤errR ∧ 0≤errI ∧ errR≤(x/2)*Fintype.card W ∧ errI≤(x/2)*Fintype.card W ∧
        MarkedRowsWithSpokes (G.comap fP) ρ d h (X.image fA) p kval (fun u=>q (gP u)) (fun u=>s (gP u)) a j errR ω H ∧
        MarkedIndicesWithSpokes ρ d h (Zinner.image gA) (fun u=>q (gP u)) (fun u=>s (gP u)) a j errI ω H
end Oberwolfach
