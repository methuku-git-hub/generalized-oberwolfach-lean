module

public import Oberwolfach.FirstVortexClassDynamicFullPackingFromRetainedTests
public import Oberwolfach.FirstVortexClassPrescribedAssignmentNoMarkedBudget
public import Oberwolfach.LongSelectedOrientedSourceWithLoadAndMatching
public import Oberwolfach.LongSelectedOrientedSourceWithLoadAndMatching
public import Oberwolfach.FirstVortexAllLevelAutomaticCoefficients
public import Oberwolfach.LongMatchingSourceCountWitness

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexClassPreparedFullPackingFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

def FirstVortexClassPreparedFullPackingOutcome
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P Sclass:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (Dv mm d m:ℕ) (β ε:ℝ)
    (Vort:Vortex U P Dv β ε mm) (F:U→SimpleGraph (Fin n))
    (hF:∀w,(F w).IsRegularOfDegree 2) (θ lamAssign eps δlocal α bmatch ρ₀ ξ Δ a γ:ℝ)
    (weight:(Fin (m+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t):Prop:=
    let ni:=@longPaddedSeedExponent K
    let hni:=@long_padded_seed_exponent_positive K
    let ℓ:=fun i=>ni i+2
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σE e)
    let selected:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (σE e)
    let Hret:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false
    let Wm:=longAssignedMarkedSeed F hF K m d θ Dv π weight
    let Wo:=longAssignedOrdinarySeed F hF K m d θ Dv P π ni hni w
    let W:=longMixedSeedWeight Wm Wo
    let Rsrc:=longRawHubResources (U:=U) π d m ℓ
    let R:=mixedCandidateResources Rsrc
    let hub:=longRawHubNames (U:=U) π d m ℓ
    ∀(Del:SimpleGraph (Fin n)) (δDel:ℝ), (∀x,(Del.degree x:ℝ)≤δDel)→
    δDel≤Δ*n→δDel≤ξ*n→
    let S:=longRawSurvivingResources P π d raw true true Del.edgeFinset
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:{v // v∈S}↪_:=Function.Embedding.subtype _
    let Q:=restrictedResourceSet R e
    let q:=survivingCandidateEmbedding R S T (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
    ∃M:Finset (RestrictedResource R e),
      (∀c∈M,0<mixedCandidateWeight W c.val) ∧
      (∀c∈M,∀c'∈M,c≠c'→Disjoint (Q c) (Q c')) ∧
      (∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card)) ∧
      (∀z:LongRetainedHubTest F hF K θ,
        let test:=longRetainedHubIndicator F hF θ hub z
        let mass:=∑c:RestrictedResource R e,test c.val*mixedCandidateWeight W c.val
        (1-γ)*mass≤∑c∈M,test c.val) ∧
      (∀z:LongRetainedHubTest F hF K θ,
        let test:=longRetainedHubIndicator F hF θ hub z
        let mass:=∑c:RestrictedResource R e,test c.val*mixedCandidateWeight W c.val
        (∑c∈M,test c.val)≤(1+γ)*mass) ∧
    (∀(Reserve:Finset (Finset (Fin n)⊕(Fin n×U))) (X:Finset (Fin n)) (Z:Finset U),
      MarkedFixedTerminalAbsorber P π d m selected Hret Reserve X Z →
      LongMatchingSourceCountWitness F hF π d m ℓ θ eps T (M.map q)) ∧
    ∀(D:Fin n→Fin n→Prop) (absorber:U→Finset (Fin n))
      (Reserve:Finset (Finset (Fin n)⊕(Fin n×U))) (X:Finset (Fin n)) (Z:Finset U),
      MarkedFixedTerminalAbsorber P π d m selected Hret Reserve X Z →
      let H:=Vort.extendedIndices 1
      let A:=Vort.extendedVertices 1
      let Used:=physicalRimCandidateUnion (markedRawSampledPhysicalEmbedding P π d raw true true)
        (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (M.map q)
      let P₀:=Sclass\Used
      let Sel:=longSelectedPhysicalGraph P π d σE
      let Kbad:=longRequiredPhysicalGraph Sclass P₀ Sel π d A D (fun x y=>Used.Adj x y)
      let Kplus:=fun Pack:Finset (Sym2 (Fin n))=>longClassInnerRequiredRepair Sclass Used Kbad A Pack
      ∃hU:0<Fintype.card U,
      LongSelectedOrientedSourceDynamicBad hU F P π d m ℓ raw t Jret σE H A Kplus Used absorber δlocal
        (fun Old Pack=>FirstVortexClassPrescribedAssignmentNoMarkedBudget P Sclass Del Used (Kplus Pack) A π d σE t Jret H (2*α) bmatch ρ₀ θ ε lamAssign Old Pack ∧ Pack=Used.edgeFinset) (M.map q)
end Oberwolfach
