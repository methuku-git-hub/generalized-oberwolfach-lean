module

public import Oberwolfach.OrdinaryVortexHistoryCrossFrontierCost
public import Oberwolfach.OrdinaryVortexBufferedDomains

@[expose] public section
/-! For cross-balance against the current protected pair, every previous
deletion is seen through its deep boundary. Older deletions vanish. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 26000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_history_deep_target_cross
    (P Q G:SimpleGraph V) (H Hs:V→U→Prop) (R:ℕ→SimpleGraph V) (S:ℕ→V→U→Prop)
    (D m:ℕ) (β ε:ℝ) (Vort:Vortex U P D β ε m) (buffer i:ℕ) (hbuffer:2≤buffer)
    (A:Finset (Sym2 V⊕(V×U))) (b:ℝ) (deepCost:ℕ→ℝ):
    let Iglobal:=Vort.extendedVertices (i+1+buffer);let Jglobal:=Vort.extendedIndices (i+1+buffer);
    let window:=Finset.Icc (i+2-buffer) i;
    let cross:=fun t=>if t∈window then 2*deepCost t else 0;
    let f:=markedVortexVertexEmbedding Vort (i+1);let g:=markedVortexHubEmbedding Vort (i+1);
    let I:=ordinaryVortexBufferedVertices Vort (i+1) buffer;let J:=ordinaryVortexBufferedHubs Vort (i+1) buffer;
    ordinaryHostResources (ordinaryHistoryRim Q R S (i+1)) (ordinaryHistorySpokes H R S (i+1))=A→
    ordinaryHostResources G Hs=A→
    (∀v∈Vort.extendedVertices (i+1),v∉Iglobal→|((Q.neighborFinset v∩Iglobal).card:ℝ)-2*(Jglobal.filter (H v)).card|≤b)→
    (∀j < i+1,R j≤ordinaryHistoryRim Q R S j ∧ ∀v u,S j v u→ ordinaryHistorySpokes H R S j v u)→
    (∀j < i+1,Disjoint (ordinaryPhysicalGraph (R j) (S j))
      (ordinaryDeepBlocker (Vort.extendedVertices (j+buffer)) (Vort.extendedIndices (j+buffer))))→
    (∀j < i+1,∀w:V⊕U,((spanningRestriction (ordinaryBoundaryGraph (R j) (S j)
      (Vort.extendedVertices (j+buffer)) (Vort.extendedIndices (j+buffer)))
      (ordinaryInnerVertices (Vort.extendedVertices (j+1)) (Vort.extendedIndices (j+1)))).degree w:ℝ)≤deepCost j)→
    ∀v,v∉I→|(((G.comap f).neighborFinset v∩I).card:ℝ)-
      2*(J.filter (fun u=>Hs (f v) (g u))).card|≤b+∑j∈Finset.range (i+1),cross j :=by
  intro Iglobal Jglobal window cross f g I J hhist hstate hinit hsub hprotect hdeep
  have hcross:∀j < i+1,∀v∈Vort.extendedVertices (i+1),v∉Iglobal→
      |(((R j).neighborFinset v∩Iglobal).card:ℝ)-2*(Jglobal.filter (S j v)).card|≤cross j:=by
    intro j hj v hv hvout
    have hIT:Iglobal⊆Vort.extendedVertices (j+buffer):=Vort.extendedVertices_subset (by omega)
    have hIX:Iglobal⊆Vort.extendedVertices (j+1):=Vort.extendedVertices_subset (by omega)
    have hJW:Jglobal⊆Vort.extendedIndices (j+buffer):=Vort.extendedIndices_subset (by omega)
    have hJZ:Jglobal⊆Vort.extendedIndices (j+1):=Vort.extendedIndices_subset (by omega)
    have hvX:v∈Vort.extendedVertices (j+1):=(Vort.extendedVertices_subset (by omega)) hv
    by_cases hw:j∈window
    · have hh:=ordinary_deep_boundary_cross_bound (R j) (S j) (Vort.extendedVertices (j+1))
        (Vort.extendedVertices (j+buffer)) Iglobal (Vort.extendedIndices (j+1))
        (Vort.extendedIndices (j+buffer)) Jglobal hIT hIX hJW hJZ v hvX (deepCost j)
        (hprotect j hj) (by intro w;convert hdeep j hj w using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
      simpa [cross,hw] using hh
    · have hjnot:¬(i+2-buffer≤j ∧ j ≤ i):=by simpa only [window,Finset.mem_Icc] using hw
      have hvT:v∈Vort.extendedVertices (j+buffer):=(Vort.extendedVertices_subset (by omega)) hv
      have hh:=ordinary_protected_inner_cross_zero (R j) (S j) (Vort.extendedVertices (j+buffer)) Iglobal
        (Vort.extendedIndices (j+buffer)) Jglobal hIT hJW v hvT (hprotect j hj)
      simpa [cross,hw] using le_of_eq hh
  have hamb:=ordinary_actual_trace_cross_balance_on_parent Q G H Hs R S A Iglobal (Vort.extendedVertices (i+1)) Jglobal
    (i+1) b cross hhist hstate hinit hsub hcross
  have hI:Iglobal⊆Vort.extendedVertices (i+1):=Vort.extendedVertices_subset (by omega)
  have hJ:Jglobal⊆Vort.extendedIndices (i+1):=Vort.extendedIndices_subset (by omega)
  have hlocal:=ordinary_cross_balance_induced_transport_on_parent G Hs (Vort.extendedVertices (i+1)) Iglobal
    (Vort.extendedIndices (i+1)) Jglobal hI hJ (b+∑j∈Finset.range (i+1),cross j) hamb
  intro v hv
  have hh:=hlocal v hv
  convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
