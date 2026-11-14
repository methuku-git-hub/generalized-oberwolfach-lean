module

public import Oberwolfach.OrdinaryMatchedRimsInComplements
public import Oberwolfach.OrdinaryExceptionalRimDegree
public import Oberwolfach.OrdinaryUncoveredRimMatchingTransfer

@[expose] public section
/-! The same physical matching, its embedded wheel packs, and the simultaneous
colour counts control the actual sample remainder outside the reference. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_same_sample_uncovered_rim_degree {n q K:ℕ}
    (Fs:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (Fs u).ConnectedComponent)
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (Old New:Fin q→Finset (Sym2 (Fin n)))
    (hpartition:∀u,(((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).edgeFinset).image
      (Sym2.map (f u))=Old u∪New u)
    (P Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (p k p₂ k₂ u t δ κ:ℝ) (hk:0≤k) (hk₂:0≤k₂) (hu:0≤u)
    (hdegree:∀a x,|(sampledColourDegree P (fun e=>(σ (Sum.inl e)).1) a x:ℝ)-
      markedExpandedPhysicalProbability p k p₂ k₂ u a*P.degree x|<t)
    (hDel:∀x,(Del.degree x:ℝ)≤δ):
    let raw:RawMarkedOutcome (Fin n) (Fin q) Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let raw':=rawMarkedDeleteRims raw Del.edgeFinset
    let Host:=ordinaryEligibleHost P π d
    let Rim:=ordinaryShiftedPairRims Host π d raw'
    let H:=rawMarkedPairSpokes π d raw' true true
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:Fin q)=>True) (fun _ (_:Fin q)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState Rim H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=Fin q) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=Fin q) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state))
    (W:∀v,OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L v→
      MarkedWheel (fun e:{e:Fin n×Fin n // Rim (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
        (fun e:{e:Fin n×Fin n // Rim (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true))
    (hW:∀v a,(W v a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L v a).1.val ∧ (W v a).2.val=v),
    let Pack:=fun v=>mixedWheelRimPack
      (fun a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L v=>longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L v a).1+2)
      (Finset.univ.image (W v)) (fun a=>(ordinaryPhysicalUnmarkedPayload π d m RM state L v a).2);
    (∀v edge,edge∈Pack v→∃e∈Old v,e.toFinset=edge)→
    (∀v,(((physicalSampledRow φ state (ordinaryPhysicalRow (.inl v)))\
      L.biUnion (physicalSampledCandidateSet φ (mixedCandidateResources RR) state)).card:ℝ)≤κ)→
    ∀x,((((longPhysicalStateGraph P σ {0,1,2,3,4}\longPhysicalStateGraph P σ {0})\
      ordinaryEmbeddedComplements Fs C f).degree x):ℝ)≤κ+(2*k+2*k₂+u)*n+3*t+(6*d+4:ℕ)+δ:=by
  intro raw raw' Host Rim H RM state RR φ L W hW Pack hPack hrow x
  let Except:=(((longPhysicalStateGraph P σ {1}⊔longPhysicalStateGraph P σ {3})⊔longPhysicalStateGraph P σ {4})⊔
      (permutationConflictGraph π (3*d+2)⊔Del))
  letI:DecidableRel Except.Adj:=Classical.decRel _
  let loss:ℝ:=(2*k+2*k₂+u)*n+3*t+(6*d+4:ℕ)+δ
  have hExcept:=ordinary_exceptional_rim_degree_bound P Del π d σ p k p₂ k₂ u t δ hk hk₂ hu hdegree hDel
  have hExcept':∀v,(Except.degree v:ℝ)≤loss:=by
    intro v
    convert hExcept v using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
  have hactive:=ordinary_sample_reference_active_rim_containment P Del π d σ
  have hpacked:=ordinary_matched_rims_embedded_in_complements (K:=K) Fs C f Old New hpartition π d m Rim H L W hW hPack
  have hh:=ordinary_uncovered_rim_degree_from_physical_matching φ (mixedCandidateResources RR) state L
    (longPhysicalStateGraph P σ {0,1,2,3,4}) (longPhysicalStateGraph P σ {0})
    (ordinaryEmbeddedComplements Fs C f) Except κ loss hrow hExcept' hactive hpacked x
  convert hh using 1 <;> (try ring) <;> congr! 6 <;> exact Subsingleton.elim _ _
end Oberwolfach
