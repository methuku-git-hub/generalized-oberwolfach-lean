module

public import Oberwolfach.OrdinaryProtectedSamplePairLocalInputs
public import Oberwolfach.OrdinaryTraceWindowPhysicalFromLocal
public import Oberwolfach.OrdinaryRawPairStateEquality
public import Oberwolfach.OrdinaryVortexBufferedNesting
public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! The original raw sample and an actual protected-pair trace have the
physical edit bound needed by the local sharp reference. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_protected_pair_trace_physical_edit
    (P Gbase F:SimpleGraph V) (Hbase:V→U→Prop) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U P D β ε m) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (K:Finset (Sym2 V⊕(V×U))) (Inner:Finset V) (Hubs:Finset U)
    (hInner:Q.extendedVertices 1⊆Inner) (hHubs:Q.extendedIndices 1⊆Hubs)
    (hr:∀v∈Inner,∀w∈Inner,((rawWheelGraph P σ)\F).Adj v w↔Gbase.Adj v w)
    (hsample:∀v∈Inner,∀u∈Hubs,rawWheelSpokes π d σ j v u↔Hbase v u)
    (hK:Disjoint K (ordinaryRootResources Inner Hubs))
    (LF:ℝ) (hLF:0≤LF) (hF:∀v,(F.degree v:ℝ)≤LF)
    (cost deepCost:ℕ→ℝ) (i buffer:ℕ) (hbuffer:2≤buffer) (hi:i+1<Q.length)
    (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop):
    let S:=Gbase\ordinaryResourceRim Gbase K;
    let H:=fun v u=>Hbase v u∧¬(Sum.inr (v,u)∈K);
    let X:=fun k=>Q.extendedVertices (k+1);let T:=fun k=>Q.extendedVertices (k+buffer);
    let Z:=fun k=>Q.extendedIndices (k+1);let W:=fun k=>Q.extendedIndices (k+buffer);
    let f:=markedVortexVertexEmbedding Q (i+1);let g:=markedVortexHubEmbedding Q (i+1);
    let ρ:=markedVortexPermutation Q π hπ (i+1);let raw:=ordinaryRawRestrictPair f g σ;
    let Jwin:=Finset.Icc (i+2-buffer) i;
    OrdinaryProtectedTrace S H X T Z W cost deepCost (i+1) A → ordinaryHostResources G Hs=A→
    ∀a:markedVortexVertexType Q (i+1)⊕markedVortexHubType Q (i+1),
      ((changed ((ordinaryPhysicalGraph (rawWheelGraph (P.comap f) raw) (rawWheelSpokes ρ d raw j)).neighborFinset a)
        ((ordinaryPhysicalGraph (G.comap f) (fun v u=>Hs (f v) (g u))).neighborFinset a)).card:ℝ)≤LF+∑j∈Jwin,cost j :=by
  intro S H X T Z W f g ρ raw Jwin htrace hstate
  have hX:Q.extendedVertices (i+1)⊆Inner:=
    (Q.extendedVertices_subset (by omega : 1 ≤ i+1)).trans hInner
  have hZ:Q.extendedIndices (i+1)⊆Hubs:=
    (Q.extendedIndices_subset (by omega : 1 ≤ i+1)).trans hHubs
  have hlocal:=ordinary_protected_sample_pair_local_inputs (rawWheelGraph P σ) F Gbase
    (rawWheelSpokes π d σ j) Hbase K (Q.extendedVertices (i+1)) Inner (Q.extendedIndices (i+1)) Hubs
    hX hZ hr hsample hK LF hLF hF
  have hnest:=ordinary_vortex_buffered_nesting P D m β ε Q i buffer hbuffer
  have hphysical:=ordinary_trace_induced_window_physical_from_local_reference (rawWheelGraph P σ) S
    (rawWheelSpokes π d σ j) H X T Z W cost deepCost i Jwin A G Hs LF
    (by intro a;convert hlocal.2 a using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    htrace hstate hnest.1 hnest.2.1 hnest.2.2.1 hnest.2.2.2.1 hnest.2.2.2.2
  have hrim:rawWheelGraph (P.comap f) raw=(rawWheelGraph P σ).induce ((X i):Set V):=by
    exact ordinary_raw_pair_graph_eq f.toEmbedding g P σ
  have hspoke:rawWheelSpokes ρ d raw j=fun (v:↥(X i)) (u:↥(Z i))=>rawWheelSpokes π d σ j v.val u.val:=by
    convert ordinary_raw_pair_spokes_eq f.toEmbedding g π ρ (by intro x;rfl) d σ j using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  intro a
  rw [hrim,hspoke]
  have hh:=hphysical a
  convert hh using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
