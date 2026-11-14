module

public import Oberwolfach.OrdinarySampleForcedSpokes

@[expose] public section
/-! The forced non-reference inner targets preserve every reference spoke,
    even if some targets are already in the old image or matching endpoints. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X V U K J I:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V]
  [Fintype U] [DecidableEq U] [DecidableEq K] [DecidableEq J] [Fintype I]

theorem ordinary_forced_inner_embedding_avoids_reference_spokes
    (F:SimpleGraph X) (a:ActualResidualData (K:=K) (J:=J) F)
    (hCycle:a.t.biUnion (fun j=>(a.C j).support.toFinset)⊆a.Cembed)
    (len:I→ℕ) (inner:∀i,Fin (len i+1)↪X) (hempty:IsEmpty I)
    (π:Equiv.Perm V) (d:ℕ) (hd:1≤d)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) t)
    (u:U) (ψ:X→V) (f:X↪V)
    (Φ g:{x:X // x∈a.remaining}→V) (B:Finset {x:X // x∈a.remaining}) (Ends:Finset V)
    (Old:Finset X) (Inner:Finset V) (Hubs:Finset U)
    (hOld:∀x∈a.oldDomain,f x=ψ x)
    (hRem:∀x:{x:X // x∈a.remaining},f x.val=Φ x)
    (hOn:∀x∈B,Φ x=g x)
    (hOutside:∀x∉B,Φ x∈rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u)
    (hImage:let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false
      let T:=ordinaryInnerSpokeTargets Inner Hubs Href u;
      B.image g=(residualSubtypeSet a.remaining a.prescribed).image (fun x=>ψ x.val)∪Ends∪((T\Old.image ψ)\Ends))
    (hEnds:Ends⊆rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u)
    (hOldBad:Disjoint ((a.oldDomain\bufferedPathStrictInterior len inner).image ψ)
      (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u)):
    ∀x,¬rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false (f x) u:=by
  let Href:=rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false
  let T:=ordinaryInnerSpokeTargets Inner Hubs Href u
  have hT:= (ordinary_sample_inner_targets_avoid_reserved π d σ Inner Hubs u).1
  have hZ:Disjoint ((T\Old.image ψ)\Ends) (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u):=
    hT.mono_left (Finset.sdiff_subset.trans Finset.sdiff_subset)
  exact ordinary_empty_final_forced_targets_avoid_reference_spokes F a hCycle len inner hempty π d hd σ t Jret u ψ f Φ g B Ends
    ((T\Old.image ψ)\Ends) hOld hRem hOn hOutside hImage hEnds hZ hOldBad
end Oberwolfach
