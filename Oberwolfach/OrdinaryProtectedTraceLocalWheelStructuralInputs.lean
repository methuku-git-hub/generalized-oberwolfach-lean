module

public import Oberwolfach.OrdinaryProtectedPairTraceLocalHost
public import Oberwolfach.OrdinaryFixedVortexConflictDegree

@[expose] public section
/-! The actual protected history supplies all graph-disjointness, conflict
degree, local balance and divisibility hypotheses for a later wheel level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_protected_trace_local_wheel_structural_inputs
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U]
    (P Gbase:SimpleGraph V) (Hbase:V→U→Prop) (D mv:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε mv) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) (d r:ℕ)
    (σ:RawWheelOutcome V U Γ Color) (K:Finset (Sym2 V⊕(V×U)))
    (hr:∀v∈Q.extendedVertices 1,∀w∈Q.extendedVertices 1,
      ((rawWheelGraph P σ)\permutationConflictGraph π (3*d)).Adj v w↔Gbase.Adj v w)
    (cost deepCost:ℕ→ℝ) (i:ℕ) (A:Finset (Sym2 V⊕(V×U)))
    (G:SimpleGraph V) (Hs:V→U→Prop):
    let S:=Gbase\ordinaryResourceRim Gbase K;
    let H:=fun v u=>Hbase v u∧¬(Sum.inr (v,u)∈K);
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+2);
    let Z:=fun k=>Q.extendedIndices (k+1);let W:=fun k=>Q.extendedIndices (k+2);
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1);
    let Gloc:=G.comap f;let Floc:=(permutationConflictGraph π (3*d)).comap f;
    let Hloc:=fun v u=>Hs (f v) (g u);
    OrdinaryProtectedTrace S H X T Z W cost deepCost (i+1) A → ordinaryHostResources G Hs=A→
    (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
    (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card)→
      Gloc≤P.comap f ∧ Disjoint Gloc Floc ∧
      (∀v,Floc.degree v≤2*(3*d)) ∧ (∀v,(Floc.degree v:ℝ)≤2*((3*d:ℕ):ℝ)) ∧
      (∀v,Gloc.degree v=2*(Finset.univ.filter (Hloc v)).card) ∧
      (∀u,r∣(Finset.univ.filter (fun v=>Hloc v u)).card) :=by
  intro S H X T Z W f g Gloc Floc Hloc htrace hstate hbal hdiv
  have hlocal:=ordinary_protected_pair_trace_local_host P Gbase Hbase D mv β ε Q π d σ K
    (Q.extendedVertices 1) (by rfl) hr cost deepCost i A G Hs htrace hstate
  have hP:Gloc≤P.comap f:=hlocal.trans sdiff_le
  have hdis:Disjoint Gloc Floc:=by
    apply disjoint_iff_inf_le.mpr
    intro v w hvw
    exact (hlocal hvw.1).2 hvw.2
  have hF:∀v,Floc.degree v≤2*(3*d):=by
    intro v
    exact ordinary_fixed_vortex_conflict_degree P D mv β ε Q π hπ (i+1) (3*d) v
  have hFr:∀v,(Floc.degree v:ℝ)≤2*((3*d:ℕ):ℝ):=by
    intro v
    exact_mod_cast hF v
  have hlocalBalance:=ordinary_vortex_trace_local_exact_balance P S G H Hs D mv β ε Q r i cost deepCost A htrace hstate hbal hdiv
  exact ⟨hP,hdis,hF,hFr,hlocalBalance.1,hlocalBalance.2⟩
end Oberwolfach
