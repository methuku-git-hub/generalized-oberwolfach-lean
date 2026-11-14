module

public import Oberwolfach.OrdinaryComplementAvoidsReferenceSpokes

@[expose] public section
/-! Adding explicitly forced targets preserves reserved spokes when those
   targets themselves avoid the reserved labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X V U K J I:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V]
  [Fintype U] [DecidableEq U] [DecidableEq K] [DecidableEq J] [Fintype I]

theorem ordinary_empty_final_forced_targets_avoid_reference_spokes
    (F:SimpleGraph X) (a:ActualResidualData (K:=K) (J:=J) F)
    (hCycle:a.t.biUnion (fun j=>(a.C j).support.toFinset)⊆a.Cembed)
    (len:I→ℕ) (inner:∀i,Fin (len i+1)↪X) (hempty:IsEmpty I)
    (π:Equiv.Perm V) (d:ℕ) (hd:1≤d)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) t)
    (u:U) (ψ:X→V) (f:X↪V)
    (Φ g:{x:X // x∈a.remaining}→V) (B:Finset {x:X // x∈a.remaining}) (Ends Z:Finset V)
    (hOld:∀x∈a.oldDomain,f x=ψ x)
    (hRem:∀x:{x:X // x∈a.remaining},f x.val=Φ x)
    (hOn:∀x∈B,Φ x=g x)
    (hOutside:∀x∉B,Φ x∈rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u)
    (hImage:B.image g=(residualSubtypeSet a.remaining a.prescribed).image (fun x=>ψ x.val)∪Ends∪Z)
    (hEnds:Ends⊆rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u)
    (hZ:Disjoint Z (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u))
    (hOldBad:Disjoint ((a.oldDomain\bufferedPathStrictInterior len inner).image ψ)
      (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u)):
    ∀x,¬rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false (f x) u:=by
  let L:=rawIntervalProtectedUnassignedList π d (fun e=>σ (Sum.inr e)) false true t Jret u
  let Bad:=rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) u
  have hInt:bufferedPathStrictInterior len inner=∅:=by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨i,_,_⟩:=Finset.mem_biUnion.mp hx
    exact hempty.false i
  have hPres:a.prescribed⊆a.oldDomain:=by
    intro x hx
    simp only [ActualResidualData.oldDomain,Finset.mem_union]
    exact Or.inl (Or.inl (Or.inl hx))
  have hList:Disjoint L Bad:=by
    simpa only [L,Bad,rawReservedSpokeList] using
      (raw_interval_protected_unassigned_avoids_labels π d hd (fun e=>σ (Sum.inr e)) false true t Jret u false).1
  have hListZ:Disjoint (L∪Z) Bad:=Finset.disjoint_union_left.mpr ⟨hList,hZ⟩
  have hOldBad':Disjoint (a.oldDomain.image ψ) Bad:=by
    simpa only [hInt,Finset.sdiff_empty] using hOldBad
  have hh:=buffered_embedding_avoids_labels a.oldDomain a.remaining a.prescribed
    (a.old_domain_union_remaining hCycle) hPres ψ f Φ g B (Ends∪Z) (L∪Z) Bad
    hOld hRem hOn (fun x hx=>Finset.mem_union_left _ (hOutside x hx))
    (by simpa only [Finset.union_assoc] using hImage)
    (by intro v hv; rcases Finset.mem_union.mp hv with hv|hv
        · exact Finset.mem_union_left _ (hEnds hv)
        · exact Finset.mem_union_right _ hv) hOldBad' hListZ
  intro x hx
  have hlabel:rawIntervalFamilyState π d (fun e=>σ (Sum.inr e)) (f x,u)=some (Sum.inr false):=
    (ordinary_reference_spoke_projection π d σ false (f x) u).mp hx
  apply hh x
  simpa only [Bad,rawReservedSpokeList,rawIntervalOrdinaryOuter,Finset.mem_filter,Finset.mem_univ,true_and] using hlabel
end Oberwolfach
