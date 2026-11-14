module

public import Oberwolfach.OrdinaryPhysicalPairHubRimPacksNamed
public import Oberwolfach.OrdinaryReservedPackagedTargetEmbeddingTracked
public import Oberwolfach.OrdinaryMatchingResidualPackagesDirectReserve

@[expose] public section
/-! A matching and coherent family together with an embedding that preserves
the exact old image from those same packages. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

def OrdinarySelectedMatchingEmbeddingTrackedResult
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Cres:∀u,Finset (F u).ConnectedComponent) (i₀:Fin K) (rsv θ lam a γ:ℝ)
    (m d:ℕ) (π:Equiv.Perm (Fin n)) (P Del Target Gbad:SimpleGraph (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) tret)
    (Inner:Finset (Fin n)) (Hubs:Finset U) (Abs:U→Finset (Fin n)) (δ:ℝ):Prop :=
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let raw':=rawMarkedDeleteRims raw Del.edgeFinset
    let state:=typedMarkedResourceState (ordinaryShiftedPairRims (ordinaryEligibleHost P π d) π d raw') (rawMarkedPairSpokes π d raw' true true)
    let R:=ordinaryMixedGenericResources
      (fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W)
      (fun i (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π
    let Cand:=PhysicalSampledCandidate (mixedCandidateResources R) state
    let Q:=physicalSampledCandidateSet φ (mixedCandidateResources R) state
    let rows:=fun j:OrdinaryPhysicalRowIndex (Fin n) U=>physicalSampledRow φ state (ordinaryPhysicalRow j);
    ∃L:Finset Cand,
      let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
      let AM:=fun u=>OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u
      let AU:=fun u=>OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u
      let payload:=fun u=>ordinaryPhysicalUnmarkedPayload π d m RM state L u
      let plen:=fun u (a:AU u)=>longPaddedSeedExponent (payload u a).1+2
      let Host:=ordinaryEligibleHost P π d
      let Rim:=ordinaryShiftedPairRims Host π d raw'
      let H:=rawMarkedPairSpokes π d raw' true true
      let ER:={e:Fin n×Fin n // Rim (Sum.inl e)}
      let ES:={e:Fin n×Fin n // Rim (Sum.inr e)}
      let MW:=MarkedWheel (fun e:ER=>e.val.1) (fun e:ER=>e.val.2) (fun e:ES=>e.val.1) (fun e:ES=>e.val.2) m π (3*d) (H false) (H true)
      let W:=fun u=>AM u→MW
      let Good:=fun u (w:W u)=>∀a,(w a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val ∧ (w a).2.val=u
      let Pack:=fun u (w:W u)=>mixedWheelRimPack (plen u) (Finset.univ.image w) (fun a=>(payload u a).2)
      let Final:=fun u=>retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false tret Jret u
      let Approx:=fun u=>{a:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (u,e))) a true}
      let root:=fun u=>retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true tret Jret u
      let S:=fun u:U=>{x:Fin n | (F u).connectedComponentMk x∉Cres u}
      let G:=fun u=>(F u).induce (S u)
      let Pos:=fun u (w:W u) (i:Approx u)=>packedPhysicalSpokePositions
        (fun e:ER=>e.val.1) (fun e:ER=>e.val.2) (fun e:ES=>e.val.1) (fun e:ES=>e.val.2)
        m (3*d) d π (H false) (H true) (Finset.univ.image w) u (root u (.inr i))
      let Arc:=rawMixedPhysicalArc Host π d raw'
      let Avail:=fun u=>rawIntervalProtectedUnassignedList π d (fun e=>raw (Sum.inr e)) false true tret Jret u
      let Reserve:=fun u=>rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) u;
      (∀x∈L,∀y∈L,x≠y→Disjoint (Q x) (Q y)) ∧
      (∀j,(((rows j)\L.biUnion Q).card:ℝ)≤(max a γ)*n) ∧
      (∀u,(1-θ-(lam+γ*(1-θ+lam)))*(n:ℝ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i)≤
        ((∑a:AU u,plen u a):ℝ) ∧
        ((∑a:AU u,plen u a):ℝ)≤
        (1-θ+(lam+γ*(1-θ+lam)))*(n:ℝ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i)) ∧
      ∃p:∀u,OrdinaryMatchedResidualHubPackage (G u) m d π (root u) Arc (Avail u) (Reserve u)
        (Good u) (Pack u) (Pos u) (plen u),
      (∀u v,u≠v→Disjoint (Pack u (p u).marker) (Pack v (p v).marker)) ∧
      (∀u,(Fintype.card {x // x∈(p u).data.remaining}:ℝ)≤δ*n) ∧
      let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false
      let T:=ordinaryInnerSpokeTargets Inner Hubs Href;
      ∃(M:U→Finset (Fin n×Fin n)) (f:∀u,↥(S u)↪Fin n),
        (∀u,u∈Hubs→M u=∅) ∧
        (∀u,prescribedMatchingEndpoints (M u)⊆Reserve u\Abs u) ∧
        (∀u,(M u).image prescribedArcPhysical⊆Gbad.edgeFinset) ∧
        (∀u v,v∈T u→∃x,f u x=v) ∧
        (∀u x,x∈(p u).data.oldDomain→f u x=(p u).ψ x) ∧
        (∀u x,f u x∉Abs u) ∧
        (∀u x y,(G u).Adj x y→Target.Adj (f u x) (f u y)) ∧
        (∀u v,u≠v→Disjoint (partialFactorPhysicalEdgesPoly ↥(S u) (G u) (f u))
          (partialFactorPhysicalEdgesPoly ↥(S v) (G v) (f v))) ∧
        (∀u,u∈Hubs→∀x,f u x∈Inner→f u x∉Reserve u) ∧
        ∃New:U→Finset (Sym2 (Fin n)),
          (∀u,((G u).edgeFinset).image (Sym2.map (f u))=(p u).data.deletedEdges.image (Sym2.map (p u).ψ)∪New u) ∧
          PairwisePhysicalDisjoint New ∧
          (∀e∈Gbad.edgeFinset,∃u,e∈New u) ∧
          (∀v,((prescribedPhysicalUnion New).degree v:ℝ)≤5*Real.sqrt δ*n)
end Oberwolfach
