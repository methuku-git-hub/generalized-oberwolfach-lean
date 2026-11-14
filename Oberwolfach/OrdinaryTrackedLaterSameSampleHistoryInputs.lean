module

public import Oberwolfach.OrdinaryTrackedHistoryConflictFreeHost
public import Oberwolfach.OrdinaryTrackedSameSampleReferenceAgreement
public import Oberwolfach.OrdinaryUniformHistorySelectedTraceInputs

@[expose] public section
/-! The corrected reservoir, tracked matching remainder and later protected
history supply the reference agreement, trace and conflict-free host on one
expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_tracked_later_same_sample_history_inputs {n q mAbs t aAbs bAbs:ℕ}
    (P S G:SimpleGraph (Fin n)) (Hs:Fin n→Fin q→Prop) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (Fs u).ConnectedComponent)
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (D mv:ℕ) (β ε:ℝ) (Vor:Vortex (Fin q) P D β ε mv)
    (K:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (Ares Wterm:Finset (Fin n)) (Bterm:Finset (Fin q))
    (ξabs editCost:ℝ) (JQ:SimpleGraph (Fin n)) (JH:Fin n→Fin q→Prop)
    (rate ξroot:ℝ) (hrate:0≤rate) (hξroot:0≤ξroot) (hSP:S≤P)
    (i L:ℕ) (A:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))):
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (σ e);
    let Bad:=permutationConflictGraph π (3*d);
    let R:=rawWheelGraph P raw;let J:=rawWheelSpokes π d raw false;
    let Q:=S\ordinaryEmbeddedComplements Fs C f;let H:=fun v u=>v∉Set.range (f u);
    let Gstart:=Q\ordinaryResourceRim Q K;let Hstart:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K);
    let X:=fun t=>Vor.extendedVertices (t+1);let T:=fun t=>Vor.extendedVertices (t+2);
    let Z:=fun t=>Vor.extendedIndices (t+1);let W:=fun t=>Vor.extendedIndices (t+2);
    let cost:=ordinaryVortexSelectedCost Vor rate;let deepCost:=ordinaryFineDeepCost Vor ξroot;
    OrdinaryCorrectedProtectedReservoirWitness 3 mAbs t aAbs bAbs ξabs (R\Bad) Bad J Ares
      (Vor.extendedVertices 1) Wterm Bterm (Vor.extendedIndices 1) K JQ JH→
    OrdinaryTrackedComplementFor P S π d σ Fs C (Vor.extendedVertices 1) (Vor.extendedIndices 1) K editCost f→
    OrdinaryUniformProtectedBalanceHistory Gstart Hstart X T Z W cost deepCost 3 (i+1) L A
      (fun t=>Vor.extendedVertices (t+2)) (fun t=>Vor.extendedVertices (t+1))
      (fun t=>Vor.extendedIndices (t+2)) (fun t=>Finset.Icc (t+3-2) t) (fun _ _=>0) (fun _ _=>0)→
    ordinaryHostResources G Hs=A→
    (∀v∈Vor.extendedVertices 1,∀w∈Vor.extendedVertices 1,(R\Bad).Adj v w↔Q.Adj v w) ∧
    (∀v∈Vor.extendedVertices 1,∀u∈Vor.extendedIndices 1,J v u↔H v u) ∧
    Disjoint K (ordinaryRootResources (Vor.extendedVertices 1) (Vor.extendedIndices 1)) ∧
    OrdinaryProtectedTrace Gstart Hstart X T Z W cost deepCost (i+1) A ∧
    (∀t∈Finset.Icc (i+2-2) i,0≤cost t ∧
      cost t≤4*rate*Fintype.card (markedVortexVertexType Vor t⊕markedVortexHubType Vor t)) ∧
    G≤P\Bad :=by
  intro raw Bad R J Q H Gstart Hstart X T Z W cost deepCost hw hf hhist hstate
  have hagree:=ordinary_tracked_same_sample_reference_agreement P S π d σ Fs C
    (Vor.extendedVertices 1) Ares Wterm (Vor.extendedIndices 1) Bterm ξabs K JQ JH editCost f hw hf
  have htrace:=ordinary_uniform_history_selected_trace_inputs Vor Gstart Hstart 3 i L A rate ξroot 0 hrate hξroot (by norm_num)
    (by convert hhist using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
  have hhost:=ordinary_tracked_history_conflict_free_host P S G Hs π d σ Fs C
    (Vor.extendedVertices 1) (Vor.extendedIndices 1) K editCost f X T Z W cost deepCost (i+1) A hSP hf
    (by convert htrace.1 using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _) hstate
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · convert hagree.1 using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _
  · convert hagree.2.1 using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _
  · convert hagree.2.2 using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _
  · convert htrace.1 using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _
  · intro t ht;simpa using htrace.2 t ht
  · convert hhost using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _
end Oberwolfach
