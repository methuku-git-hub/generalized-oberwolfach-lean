module

public import Oberwolfach.CompletionRestrictedFreeHubLoadLocal
public import Oberwolfach.FirstVortexResidualCompletionOrientedRestricted
public import Oberwolfach.PrescribedBadEdgeAssignments

@[expose] public section
/-! For the actual completion maps, outside-root image load is bounded by
prescribed images, bad-edge endpoints and tracked free occurrences. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexRestrictedOutsideLoadLocalFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_restricted_completion_outside_load_local
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (K J:U→Type) [∀w,DecidableEq (K w)] [∀w,DecidableEq (J w)]
    (a:∀w,ActualResidualData (K:=K w) (J:=J w) (F w)) (ψ:U→Fin n→Fin n)
    (Kbad:SimpleGraph (Fin n)) (assign:Sym2 (Fin n)→U) (orient:Sym2 (Fin n)→Fin n×Fin n)
    (Z:U→Finset (Fin n)) (I:Finset (Fin n)) (H:Finset U)
    (B:∀w,Finset {x // x∈(a w).remaining}) (g Φ:∀w,{x // x∈(a w).remaining}→Fin n)
    (aScale κ P Q:ℝ)
    (hOrient:∀e∈Kbad.edgeFinset,prescribedArcPhysical (orient e)=e)
    (hfixed:∀w x,x∈B w→Φ w x=g w x)
    (hforced:∀w,(B w).image (g w)=
      (residualSubtypeSet (a w).remaining (a w).prescribed).image (fun x=>ψ w x.1)∪
        prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient w)∪Z w)
    (hZ:∀w,Z w⊆I)
    (hpre:∀v,((H.filter (fun w=>v∈
      (residualSubtypeSet (a w).remaining (a w).prescribed).image (fun x=>ψ w x.1))).card:ℝ)≤P)
    (hK:∀v,v∉I→(Kbad.degree v:ℝ)≤Q)
    (hfree:∀v,((((Finset.univ.filter (fun z:(Σw,{x // x∈(a w).remaining})=>z.2∉B z.1)).filter
      (fun z=>z.1∈H)).filter (fun z=>Φ z.1 z.2=v)).card:ℝ)≤κ*aScale+1):
    ∀v,v∉I→((H.filter (fun w=>v∈Finset.univ.image (Φ w))).card:ℝ)≤P+Q+(κ*aScale+1) :=by
  have hassigned:=prescribed_assigned_arcs_physical Kbad assign orient hOrient
  have hsub:∀w,(prescribedAssignedArcs Kbad assign orient w).image prescribedArcPhysical⊆Kbad.edgeFinset:=by
    intro w e he
    exact (hassigned.1 w e he).1
  exact completion_restricted_image_load_outside_from_occurrences_local
    (fun w=>{x // x∈(a w).remaining}) H B Φ g
    (fun w=>(residualSubtypeSet (a w).remaining (a w).prescribed).image (fun x=>ψ w x.1)) Z
    (prescribedAssignedArcs Kbad assign orient) Kbad hfixed hforced hsub hassigned.2.2 I hZ P Q (κ*aScale+1) hpre hK hfree
end Oberwolfach
