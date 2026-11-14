module

public import Oberwolfach.OrdinaryProtectedTraceHostLe
public import Oberwolfach.OrdinaryRawIntervalGeometry
public import Oberwolfach.OrdinaryVortexTraceLocalExactBalance

@[expose] public section
/-! A protected trace lies in the original host locally even if the edited
ambient target has edges outside that host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_protected_pair_trace_local_host
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U]
    (P Gbase:SimpleGraph V) (Hbase:V→U→Prop) (D mv:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε mv) (π:Equiv.Perm V) (d:ℕ)
    (σ:RawWheelOutcome V U Γ Color) (K:Finset (Sym2 V⊕(V×U)))
    (Inner:Finset V) (hInner:Q.extendedVertices 1⊆Inner)
    (hr:∀v∈Inner,∀w∈Inner,
      ((rawWheelGraph P σ)\permutationConflictGraph π (3*d)).Adj v w↔Gbase.Adj v w)
    (cost deepCost:ℕ→ℝ) (i:ℕ) (A:Finset (Sym2 V⊕(V×U)))
    (G:SimpleGraph V) (Hs:V→U→Prop):
    let S:=Gbase\ordinaryResourceRim Gbase K;
    let H:=fun v u=>Hbase v u∧¬(Sum.inr (v,u)∈K);
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+2);
    let Z:=fun k=>Q.extendedIndices (k+1);let W:=fun k=>Q.extendedIndices (k+2);
    let f:=markedVortexVertexEmbedding Q (i+1);
    OrdinaryProtectedTrace S H X T Z W cost deepCost (i+1) A→ ordinaryHostResources G Hs=A→
    (G.comap f)≤(P.comap f)\((permutationConflictGraph π (3*d)).comap f) :=by
  intro S H X T Z W f htrace hstate
  have hGle:G≤Gbase:=
    (ordinary_protected_trace_host_le S G H Hs X T Z W cost deepCost (i+1) A htrace hstate).trans sdiff_le
  intro v w hvw
  have hv:(f v)∈Inner:=hInner ((Q.extendedVertices_subset (by omega : 1 ≤ i+1)) v.property)
  have hw:(f w)∈Inner:=hInner ((Q.extendedVertices_subset (by omega : 1 ≤ i+1)) w.property)
  have hfrom:= (hr (f v) hv (f w) hw).mpr (hGle hvw)
  exact ⟨(retainedGraph_le P (fun e=>σ (Sum.inl e))) hfrom.1,hfrom.2⟩
end Oberwolfach
