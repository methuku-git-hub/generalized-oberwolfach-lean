module

public import Oberwolfach.OrdinaryFreshTriangleBoundaryEventInside
public import Oberwolfach.OrdinaryVortexTraceLocalExactBalance
public import Oberwolfach.OrdinaryProtectedTraceHostLe
public import Oberwolfach.OrdinaryPhysicalInnerRestriction

@[expose] public section
/-! On an actual protected trace, the fresh boundary bundle supplies the
    triangle finish inputs using balance and avoidance from that same host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_trace_triangle_fresh_finish_inputs
    (P JQ:SimpleGraph V) (JH:V→U→Prop) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε m) (π:Equiv.Perm V) (d:ℕ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (K:Finset (Sym2 V⊕(V×U))) (cost deepCost:ℕ→ℝ) (i:ℕ)
    (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop)
    (γ κ b B εf ηHub ζfresh p εres εsup βe βh τ ν:ℝ):
    let F:=permutationConflictGraph π (3*d)
    let R:=rawWheelGraph P raw;let J:=rawWheelSpokes π d raw j
    let S:=(R\F)\JQ;let H:=fun v u=>J v u∧¬JH v u
    let S₀:=S\ordinaryResourceRim S K;let H₀:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K)
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+2)
    let Z:=fun k=>Q.extendedIndices (k+1);let W:=fun k=>Q.extendedIndices (k+2)
    let I:=markedVortexInnerVertices Q (i+1);let Bset:=markedVortexInnerHubs Q (i+1)
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1)
    let Q₀:=G.comap f;let Floc:=F.comap f;let Hloc:=fun v u=>Hs (f v) (g u)
    let Qinner:=spanningRestriction Q₀ I;let Hinner:=fun v u=>Hloc v u∧v∈I∧u∈Bset;
    OrdinaryProtectedTrace S₀ H₀ X T Z W cost deepCost (i+1) A → ordinaryHostResources G Hs=A→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀u,3∣(Finset.univ.filter (fun v=>Hs v u)).card)→
    ∀(data:MixedFreshParentDataInsideRoots γ κ b B εf ηHub Qinner Floc (ordinaryPhysicalGraph Qinner Hinner)
      (ordinaryPhysicalGraph Floc (fun _ _=>False)) (Function.Embedding.inl:markedVortexVertexType Q (i+1)↪_)
      (ordinaryBoundaryHubSet Hloc Bset I) (fun k=>(ordinaryBoundaryRimSet Q₀ I k).image Sum.inl)
      (fun k=>(ordinaryBoundaryRowSet Hloc I Bset k).image Sum.inr))
      (σfresh:Sym2 (markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1))→Bool),
    OrdinaryFreshTriangleBoundaryEventInside Q₀ Qinner Floc Hloc Hinner I Bset γ κ b B εf ηHub ζfresh p εres εsup βe βh data σfresh→
    OrdinaryTriangleFinishNumbers (V:=markedVortexVertexType Q (i+1)) (U:=markedVortexHubType Q (i+1)) γ κ ζfresh p εsup τ ν→
    OrdinaryTriangleFinishSampleInputsInside Q₀ Qinner Floc Hloc Hinner I Bset σfresh γ κ b B εf ηHub ζfresh p εsup τ ν :=by
  intro F R J S H S₀ H₀ X T Z W I Bset f g Q₀ Floc Hloc Qinner Hinner htrace hstate hbal hdiv data σfresh hfresh hnum
  have hS₀le:S₀≤P\F:=by
    intro v w hvw
    exact ⟨(retainedGraph_le P _) hvw.1.1.1,hvw.1.1.2⟩
  have hG0:=ordinary_protected_trace_host_le S₀ G H₀ Hs X T Z W cost deepCost (i+1) A htrace hstate
  have hQle:Q₀≤(P.comap f)\Floc:=by
    intro v w hvw
    exact hS₀le (hG0 hvw)
  have hdis:Disjoint Q₀ Floc:=by
    apply disjoint_iff_inf_le.mpr
    intro v w hvw
    exact (hQle hvw.1).2 hvw.2
  have hlocal:=ordinary_vortex_trace_local_exact_balance P S₀ G H₀ Hs D m β ε Q 3 i cost deepCost A htrace hstate hbal hdiv
  have hbase:ordinaryPhysicalGraph Qinner Hinner≤spanningRestriction (ordinaryPhysicalGraph Q₀ Hloc) (ordinaryInnerVertices I Bset):=by
    rw [ordinary_physical_inner_restriction]
  exact ordinary_triangle_finish_inputs_from_fresh_event_inside Q₀ Qinner Floc Hloc Hinner I Bset
    γ κ b B εf ηHub ζfresh p εres εsup βe βh τ ν data σfresh hfresh hnum hbase hdis
    (by intro v; have hh:=hlocal.1 v; convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro u; have hh:=hlocal.2 u; convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
end Oberwolfach
