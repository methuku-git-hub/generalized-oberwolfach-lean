module

public import Oberwolfach.FirstVortexClassPrescribedAssignmentNoMarkedBudget

@[expose] public section
/-! The reserved-edge assignment itself is independent of which physical
edges are forbidden to the free part: each prescribed arc is a Kbad edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstClassAssignmentChangeDeletionFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_class_assignment_change_deletion
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P S Del Del' Used Kbad:SimpleGraph (Fin n)) (I:Finset (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t)
    (H:Finset U) (α b ρ₀ θ ε lam:ℝ) (Old:U→Finset (Fin n)) (Pack:Finset (Sym2 (Fin n))):
    FirstVortexClassPrescribedAssignmentNoMarkedBudget P S Del Used Kbad I π d σE t Jret H α b ρ₀ θ ε lam Old Pack→
    FirstVortexClassPrescribedAssignmentNoMarkedBudget P S Del' Used Kbad I π d σE t Jret H α b ρ₀ θ ε lam Old Pack:=by
  intro h
  unfold FirstVortexClassPrescribedAssignmentNoMarkedBudget at h ⊢
  have hdec:firstVortexClassPrescribedNoMarkedFin n=firstClassAssignmentChangeDeletionFin n:=Subsingleton.elim _ _
  try rw [hdec] at h ⊢
  rcases h with ⟨hdegree,hcard,hpack,hJ,hKJ,hUsedJ,hout,hshield,hlabels,assign,orient,horient,hallowed,hconf,hload,hold,hinner,hmatch,hcap⟩
  refine ⟨hdegree,hcard,hpack,hJ,hKJ,hUsedJ,hout,hshield,hlabels,assign,orient,?_,hallowed,hconf,hload,hold,hinner,hmatch,hcap⟩
  intro e he
  have h:=horient e he
  refine ⟨h.1,Or.inr ?_⟩
  rw [←h.1] at he
  change s((orient e).1,(orient e).2)∈Kbad.edgeFinset at he
  exact SimpleGraph.mem_edgeFinset.mp he
end Oberwolfach
