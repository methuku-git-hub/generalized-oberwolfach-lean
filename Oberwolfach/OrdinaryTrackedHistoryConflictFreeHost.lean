module

public import Oberwolfach.OrdinaryTrackedComplementWitness
public import Oberwolfach.OrdinaryProtectedTraceHostLe

@[expose] public section
/-! Every later protected host remains inside the original host and avoids
all conflicts when it starts from the tracked matching remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_tracked_history_conflict_free_host {n q:ℕ}
    (P S G:SimpleGraph (Fin n)) (Hs:Fin n→Fin q→Prop) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (Fs u).ConnectedComponent)
    (Inner:Finset (Fin n)) (Hubs:Finset (Fin q)) (K:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (editCost:ℝ) (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (X T:ℕ→Finset (Fin n)) (Z W:ℕ→Finset (Fin q)) (cost deepCost:ℕ→ℝ)
    (i:ℕ) (A:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (hSP:S≤P):
    let Bad:=permutationConflictGraph π (3*d);
    let Q:=S\ordinaryEmbeddedComplements Fs C f;
    let H:=fun v u=>v∉Set.range (f u);
    let Gstart:=Q\ordinaryResourceRim Q K;
    let Hstart:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K);
    OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs K editCost f→
    OrdinaryProtectedTrace Gstart Hstart X T Z W cost deepCost i A→
    ordinaryHostResources G Hs=A→G≤P\Bad :=by
  intro Bad Q H Gstart Hstart hf htrace hstate
  have hf':=hf
  dsimp only [OrdinaryTrackedComplementFor] at hf'
  obtain ⟨_,_,_,_,_,hdis,_⟩:=hf'
  have hG:=ordinary_protected_trace_host_le Gstart G Hstart Hs X T Z W cost deepCost i A htrace hstate
  have hGQ:G≤Q:=hG.trans sdiff_le
  have hQP:Q≤P:=sdiff_le.trans hSP
  intro v w hvw
  exact ⟨hQP (hGQ hvw),fun hbad=>(disjoint_iff_inf_le.mp hdis) ⟨hGQ hvw,hbad⟩⟩
end Oberwolfach
