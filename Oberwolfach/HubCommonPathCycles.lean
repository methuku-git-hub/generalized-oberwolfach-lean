module

public import Oberwolfach.RootFirstCommonPaths
public import Oberwolfach.PairedAbsorberCounts

@[expose] public section

/-! Actual marked cycles at a fixed hub supplied by a common marked path.
Root spokes are required only here, after the two roots have been chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K : Type*} [Fintype V] [DecidableEq V]
  {tail head : E → V} {ktail khead : K → V} {m : ℕ}
  {π : Equiv.Perm V} {b : ℕ} {H₀ Hₖ : V → U → Prop}

abbrev HubMarkedCycle (tail head : E → V) (ktail khead : K → V)
    (m : ℕ) (π : Equiv.Perm V) (b : ℕ) (H₀ Hₖ : V → U → Prop) (w : U) :=
  {f : Fin (m+1) → V // IsMarkedCycleTuple tail head ktail khead m π b f ∧
    MarkedHubCompatible H₀ Hₖ f w}

def hubMarkedCycleVertices (w : U)
    (C : HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w) : Finset V :=
  Finset.univ.image C.val

theorem rootedCycleOrder_vertices (σ : Equiv.Perm (Fin (m+1))) (v : V) (z : Fin m → V) :
    Finset.univ.image (rootedCycleOrder σ v z)=insert v (Finset.univ.image z) := by
  ext u
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_insert]
  constructor
  · rintro ⟨i,hi⟩
    rcases Fin.eq_zero_or_eq_succ (σ i) with he|⟨j,hj⟩
    · exact Or.inl (by simpa only [rootedCycleOrder,he,Fin.cases_zero] using hi.symm)
    · exact Or.inr ⟨j,by simpa only [rootedCycleOrder,hj,Fin.cases_succ] using hi⟩
  · rintro (rfl|⟨j,rfl⟩)
    · exact ⟨σ.symm 0,by simp only [rootedCycleOrder,Equiv.apply_symm_apply,Fin.cases_zero]⟩
    · exact ⟨σ.symm j.succ,by simp only [rootedCycleOrder,Equiv.apply_symm_apply,Fin.cases_succ]⟩

theorem rootFirstCommonMarkedPath_hub_cycles (hm : 3<m+1)
    (w : U) (j : Bool) (v v' : V)
    (hv : if j then Hₖ v w else H₀ v w)
    (hv' : if j then Hₖ v' w else H₀ v' w)
    (z : RootFirstCommonMarkedPath tail head ktail khead m π b H₀ Hₖ j v v' w w) :
    (∃ C : HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w,
      hubMarkedCycleVertices w C=insert v (Finset.univ.image z.val)) ∧
    (∃ C : HubMarkedCycle tail head ktail khead m π b H₀ Hₖ w,
      hubMarkedCycleVertices w C=insert v' (Finset.univ.image z.val)) := by
  have hr : (if markedPositionType ((markedRootOrder m j).symm 0) then Hₖ v w else H₀ v w) ∧
      (if markedPositionType ((markedRootOrder m j).symm 0) then Hₖ v w else H₀ v w) ∧
      (if markedPositionType ((markedRootOrder m j).symm 0) then Hₖ v' w else H₀ v' w) ∧
      (if markedPositionType ((markedRootOrder m j).symm 0) then Hₖ v' w else H₀ v' w) := by
    rw [markedRootOrder_type m hm j]
    exact ⟨hv,hv,hv',hv'⟩
  let Z := (rootFirstCommonMarkedPathEquiv j v v' w w) z
  let P := orderedCommonMarkedPath_to_pair hr Z
  constructor
  · refine ⟨⟨P.val.1.val,P.val.1.property,P.property.2.2.2.1⟩,?_⟩
    change Finset.univ.image (rootedCycleOrder (markedRootOrder m j) v z.val)=_
    exact rootedCycleOrder_vertices _ _ _
  · refine ⟨⟨P.val.2.val,P.val.2.property,P.property.2.2.2.2.2.1⟩,?_⟩
    change Finset.univ.image (rootedCycleOrder (markedRootOrder m j) v' z.val)=_
    exact rootedCycleOrder_vertices _ _ _

end Oberwolfach
