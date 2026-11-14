module

public import Oberwolfach.CompletionRestrictedFreeHubLoad
public import Oberwolfach.ActualResidualPhysicalUnionOutside
public import Oberwolfach.PrescribedBadEdgeAssignments

@[expose] public section
/-! Tracking all hubs also improves the global completion loss, without a square root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexTrackedGlobalImageAndDegreeFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem first_vortex_tracked_global_image_and_degree
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (K J:U→Type) [∀w,DecidableEq (K w)] [∀w,DecidableEq (J w)]
    (a:∀w,ActualResidualData (K:=K w) (J:=J w) (F w)) (ψ:U→Fin n→Fin n)
    (Kbad:SimpleGraph (Fin n)) (assign:Sym2 (Fin n)→U) (orient:Sym2 (Fin n)→Fin n×Fin n)
    (Z:U→Finset (Fin n)) (B:∀w,Finset {x // x∈(a w).remaining}) (g Φ:∀w,{x // x∈(a w).remaining}→Fin n)
    (Qres:∀w,SimpleGraph {x // x∈(a w).remaining})
    (hQres:∀w,Qres w=((a w).graph).induce (↑(a w).remaining:Set (Fin n))) (hinj:∀w,Function.Injective (Φ w))
    (δ κ:ℝ)
    (hOrient:∀e∈Kbad.edgeFinset,prescribedArcPhysical (orient e)=e)
    (hfixed:∀w x,x∈B w→Φ w x=g w x)
    (hforced:∀w,(B w).image (g w)=(residualSubtypeSet (a w).remaining (a w).prescribed).image (fun x=>ψ w x.1)∪
      prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient w)∪Z w)
    (hglobal:∀v,((Finset.univ.filter (fun w=>v∈(residualSubtypeSet (a w).remaining (a w).prescribed).image (fun x=>ψ w x.1))).card:ℝ)+
      Kbad.degree v+((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤δ*n)
    (hfree:∀v,((((Finset.univ.filter (fun z:(Σw,{x // x∈(a w).remaining})=>z.2∉B z.1)).filter
      (fun z=>z.1∈(Finset.univ:Finset U))).filter (fun z=>Φ z.1 z.2=v)).card:ℝ)≤κ*n+1):
    (∀v,((Finset.univ.filter (fun w=>v∈Finset.univ.image (Φ w))).card:ℝ)≤δ*n+(κ*n+1)) ∧
    let E:U→Finset (Sym2 (Fin n)):=fun w=>(Qres w).edgeFinset.image (Sym2.map (Φ w));
    ∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤2*(δ*n+(κ*n+1)):=by
  have hassigned:=prescribed_assigned_arcs_physical Kbad assign orient hOrient
  have hsub:∀w,(prescribedAssignedArcs Kbad assign orient w).image prescribedArcPhysical⊆Kbad.edgeFinset:=by
    intro w e he;exact (hassigned.1 w e he).1
  have himage:∀v,((Finset.univ.filter (fun w=>v∈Finset.univ.image (Φ w))).card:ℝ)≤δ*n+(κ*n+1):=by
    intro v
    have hh:=completion_restricted_image_load (fun w=>{x // x∈(a w).remaining}) Finset.univ B Φ g
      (fun w=>(residualSubtypeSet (a w).remaining (a w).prescribed).image (fun x=>ψ w x.1)) Z
      (prescribedAssignedArcs Kbad assign orient) Kbad hfixed hforced hsub hassigned.2.2 v
    have hf:=completion_restricted_free_hub_load (fun w=>{x // x∈(a w).remaining}) Finset.univ B Φ v
    have hg:=hglobal v
    have hs:=hfree v
    push_cast at hh
    linarith
  refine ⟨himage,?_⟩
  intro E v
  exact actual_residual_physical_union_degree_from_image_load F hF _ J a Qres hQres Φ hinj v _ (himage v)
end Oberwolfach
