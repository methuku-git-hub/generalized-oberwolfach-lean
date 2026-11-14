module

public import Oberwolfach.OrdinaryComplementRemainderDecomposition
public import Oberwolfach.OrdinaryResourceSubgraphs

@[expose] public section
/-! Exact protected-pair agreement with the conflict-deleted sample implies
local conflict-freeness of the actual complement after reserving resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_protected_complement_local_conflict_free {n q:ℕ}
    (Target Sample Fbad:SimpleGraph (Fin n))
    (Fs:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (Fs u).ConnectedComponent)
    (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (K:Finset (Sym2 (Fin n)⊕(Fin n×Fin q)))
    (X Inner:Finset (Fin n)) (hX:X⊆Inner)
    (hr:∀v∈Inner,∀w∈Inner,
      (Target\ordinaryEmbeddedComplements Fs C f).Adj v w↔(Sample\Fbad).Adj v w):
    let Q:=Target\ordinaryEmbeddedComplements Fs C f;
    Disjoint ((Q\ordinaryResourceRim Q K).induce (X:Set (Fin n))) (Fbad.induce (X:Set (Fin n))) :=by
  intro Q
  apply disjoint_iff_inf_le.mpr
  intro v w hvw
  have hq:Q.Adj v.val w.val:=hvw.1.1
  have hbad:Fbad.Adj v.val w.val:=hvw.2
  exact ((hr v.val (hX v.property) w.val (hX w.property)).mp hq).2 hbad
end Oberwolfach
