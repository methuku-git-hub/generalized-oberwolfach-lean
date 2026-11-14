module

public import Oberwolfach.OrdinaryEmptyFinalReservedSpokes
public import Oberwolfach.OrdinaryReferenceSpokeProjection
public import Oberwolfach.RawReservedSpokeList

@[expose] public section
/-! The same-sample empty-final complement embedding avoids the selected
reference reservoir's reserved spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X V U K J I:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V]
  [Fintype U] [DecidableEq U] [DecidableEq K] [DecidableEq J] [Fintype I]

theorem ordinary_empty_final_complement_avoids_reference_spokes
    (F:SimpleGraph X) (a:ActualResidualData (K:=K) (J:=J) F)
    (hCycle:a.t.biUnion (fun j=>(a.C j).support.toFinset)⊆a.Cembed)
    (len:I→ℕ) (inner:∀i,Fin (len i+1)↪X) (hempty:IsEmpty I)
    (π:Equiv.Perm V) (d:ℕ) (hd:1≤d)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) t)
    (u:U) (ψ:X→V) (f:X↪V)
    (Φ g:{x:X // x∈a.remaining}→V) (B:Finset {x:X // x∈a.remaining}) (Ends:Finset V)
    (hOld:∀x∈a.oldDomain,f x=ψ x)
    (hRem:∀x:{x:X // x∈a.remaining},f x.val=Φ x)
    (hOn:∀x∈B,Φ x=g x)
    (hOutside:∀x∉B,Φ x∈rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u)
    (hImage:B.image g=(residualSubtypeSet a.remaining a.prescribed).image (fun x=>ψ x.val)∪Ends)
    (hEnds:Ends⊆rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u)
    (hOldBad:Disjoint ((a.oldDomain\bufferedPathStrictInterior len inner).image ψ)
      (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u)):
    ∀x,¬rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false (f x) u:=by
  have hh:=ordinary_empty_final_residual_avoids_reserved_spokes F a hCycle len inner hempty π d hd
    (fun e=>σ (Sum.inr e)) false true t Jret u false ψ f Φ g B Ends hOld hRem hOn hOutside hImage hEnds
    (by simpa only [rawReservedSpokeList] using hOldBad)
  intro x hx
  exact hh x ((ordinary_reference_spoke_projection π d σ false (f x) u).mp hx)
end Oberwolfach
