module

public import Oberwolfach.OrdinarySameSampleUncoveredConflictReference
public import Oberwolfach.OrdinaryUsedSelectedReferenceFromOld
public import Oberwolfach.OrdinaryComplementReferencePhysicalEdit
public import Oberwolfach.OrdinarySharedSamplePhysicalInclusion

@[expose] public section
/-! The actual complement's global physical edit follows from the same
matching's uncovered rows, old edges and residual union, plus reference tests. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_actual_complement_physical_from_matching {n q r K : ℕ}
    {A B J : Fin q → Type} [∀u,Fintype (A u)] [∀u,DecidableEq (A u)]
    [∀u,DecidableEq (B u)] [∀u,DecidableEq (J u)]
    (P Target Host Del Fbad : SimpleGraph (Fin n)) (hHost : Host≤P)
    (π : Equiv.Perm (Fin n)) (d m : ℕ)
    (σ : ∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs : Fin q→SimpleGraph (Fin n)) (hFs : ∀u,(Fs u).IsRegularOfDegree 2)
    (C : ∀u,Finset (Fs u).ConnectedComponent) (hsize : ∀u (c:↥(C u)),Fintype.card c.val=r)
    (f : ∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (data : ∀u,ActualResidualData (K:=A u⊕B u) (J:=J u)
      ((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}))
    (hempty : ∀u,IsEmpty (A u)) (hs : ∀u,(data u).s₁=firstSumIndices)
    (ψ : ∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}→Fin n)
    (New : Fin q→Finset (Sym2 (Fin n)))
    (hdir : ∀u,ActualOldImageDirected (data u) (ψ u) (rawMixedPhysicalArc Host π d
      (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset)))
    (hpartition : ∀u,(((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).edgeFinset).image
      (Sym2.map (f u))=(data u).deletedEdges.image (Sym2.map (ψ u)) ∪ New u)
    (hTarget : Target.IsRegularOfDegree (2*q))
    (hC : ∀u x y,((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}).Adj x y→Target.Adj (f u x) (f u y))
    (hCC : ∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x:Fin n // (Fs u).connectedComponentMk x∉C u}
        ((Fs u).induce {x | (Fs u).connectedComponentMk x∉C u}) (f u))
      (partialFactorPhysicalEdgesPoly {x:Fin n // (Fs v).connectedComponentMk x∉C v}
        ((Fs v).induce {x | (Fs v).connectedComponentMk x∉C v}) (f v)))
    (p k p₂ k₂ u t δ κ LF loss b rsv e tcol : ℝ)
    (hk : 0≤k) (hk₂ : 0≤k₂) (hu : 0≤u) (ht : 0≤t) (hδ : 0≤δ) (hκ : 0≤κ) (hLF : 0≤LF)
    (hloss : 0≤loss) (hb : 0≤b)
    (hcolour : ∀a x,|(sampledColourDegree P (fun e=>(σ (Sum.inl e)).1) a x:ℝ)-
      markedExpandedPhysicalProbability p k p₂ k₂ u a*P.degree x|<t)
    (hDel : ∀x,(Del.degree x:ℝ)≤δ) (hF : ∀x,(Fbad.degree x:ℝ)≤LF)
    (hNew : ∀x,((prescribedPhysicalUnion New).degree x:ℝ)≤loss)
    (hCard : ∀v,((r:ℕ):ℝ)*(C v).card=rsv*n) :
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4}
    let Ref:=rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (σ e))\Fbad
    let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false
    let raw:RawMarkedOutcome (Fin n) (Fin q) Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let raw':=rawMarkedDeleteRims raw Del.edgeFinset
    let MatchHost:=ordinaryEligibleHost P π d
    let Rim:=ordinaryShiftedPairRims MatchHost π d raw'
    let H:=rawMarkedPairSpokes π d raw' true true
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:Fin q)=>True) (fun _ (_:Fin q)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState Rim H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=Fin q) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=Fin q) π;
    (∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤b)→
    (∀u x,¬Href (f u x) u)→
    (∀v,|((Ref.degree v:ℝ)-2*((Finset.univ.filter (Href v)).card:ℝ))|≤e)→
    (∀v,|((Finset.univ.filter (fun x=>Href x v)).card:ℝ)-rsv*n|≤tcol)→
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state))
    (W:∀v,OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L v→
      MarkedWheel (fun e:{e:Fin n×Fin n // Rim (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
        (fun e:{e:Fin n×Fin n // Rim (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true))
    (hW:∀v a,(W v a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L v a).1.val ∧ (W v a).2.val=v),
    let Pack:=fun v=>mixedWheelRimPack
      (fun a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L v=>longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L v a).1+2)
      (Finset.univ.image (W v)) (fun a=>(ordinaryPhysicalUnmarkedPayload π d m RM state L v a).2);
    (∀v edge,edge∈Pack v→∃e∈(data v).deletedEdges.image (Sym2.map (ψ v)),e.toFinset=edge)→
    (∀v,(((physicalSampledRow φ state (ordinaryPhysicalRow (.inl v)))\
      L.biUnion (physicalSampledCandidateSet φ (mixedCandidateResources RR) state)).card:ℝ)≤κ)→
    ∀(Kres:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))),
    Kres⊆ordinaryHostResources (Target\ordinaryEmbeddedComplements Fs C f) (fun v u=>v∉Set.range (f u))→
    let κref:=κ+(2*k+2*k₂+u)*n+3*t+(6*d+4:ℕ)+δ+LF
    let lrim:=b+κref+loss
    let lspoke:=max ((lrim+e)/2) tcol;
    ∀w:Fin n⊕Fin q,((changed ((ordinaryPhysicalGraph Ref Href).neighborFinset w)
      ((ordinaryPhysicalGraph ((Target\ordinaryEmbeddedComplements Fs C f)\ordinaryResourceRim (Target\ordinaryEmbeddedComplements Fs C f) Kres)
        (fun v u=>v∉Set.range (f u)∧¬(Sum.inr (v,u)∈Kres))).neighborFinset w)).card:ℝ)≤
      lrim+lspoke+(ordinaryResourceRows Kres).card+(ordinaryResourceHubs Kres).card :=by
  intro Sample Ref Href raw raw' MatchHost Rim H RM state RR φ hEdit hAvoid hRefBal hCols L W hW Pack hPack hrow Kres hK κref lrim lspoke
  have hRef : Ref≤Sample := sdiff_le.trans (ordinary_shared_sample_reference_graph_le_class P σ)
  have hκref : 0≤κref := by dsimp [κref];positivity
  have hUncover : ∀x,(((Sample\Ref)\ordinaryEmbeddedComplements Fs C f).degree x:ℝ)≤κref := by
    intro x
    have hh:=ordinary_same_sample_uncovered_conflict_reference_degree (K:=K) Fs C f
      (fun u=>(data u).deletedEdges.image (Sym2.map (ψ u))) New hpartition P Del Fbad π d m σ
      p k p₂ k₂ u t δ κ LF hk hk₂ hu hcolour hDel hF L W hW hPack hrow x
    rw [←ordinary_shared_sample_reference_graph_eq_state_zero] at hh
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hUsed:=ordinary_used_selected_reference_degree_from_old P Host Del Ref hHost π d σ sdiff_le
    Fs C f data hempty hs ψ New hdir hpartition loss hNew
  have hh:=ordinary_complement_reference_physical_edit Target Sample Ref hRef hTarget Fs hFs C hsize f hC hCC
    Href rsv b κref loss e tcol hb hκref hloss hAvoid hCard hEdit
    (by intro v;convert hUncover v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v;convert hUsed v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v;convert hRefBal v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v;convert hCols v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) Kres hK
  intro w
  convert hh w using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
