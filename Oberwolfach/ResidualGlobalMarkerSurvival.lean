module

public import Oberwolfach.ResidualCentralPathInterior
public import Oberwolfach.ResidualDeletionLocalization

@[expose] public section
/-! The survival of a selected-path marker is determined by the selected
runs on its own path, even in the presence of the global deletion. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

def pathFamilyLocalDeletion (F:SimpleGraph V) (s₁:Finset I) (u v:I→V)
    (P:∀i,F.Walk (u i) (v i)) (c d:ℕ) (T:I→Finset ℕ)
    (hT:∀i,T i⊆Finset.range d) (i:I):Finset V :=
  if i∈s₁ then centralPathInterior (P i) c d else selectedRunInteriors (P i) c d (T i) (hT i)

theorem path_family_local_deletion_subset (F:SimpleGraph V) (s₁:Finset I)
    (u v:I→V) (P:∀i,F.Walk (u i) (v i)) (c d:ℕ)
    (T:I→Finset ℕ) (hT:∀i,T i⊆Finset.range d)
    (i:I) (hlen:(P i).length=c*d+4):
    pathFamilyLocalDeletion F s₁ u v P c d T hT i ⊆ (P i).support.toFinset := by
  by_cases hi:i∈s₁
  · simpa [pathFamilyLocalDeletion,hi] using central_path_interior_subset (P i) c d hlen
  · simpa [pathFamilyLocalDeletion,hi] using selected_run_interiors_subset_extended_path (P i) c d hlen (T i) (hT i)

theorem selected_marker_survives_global_deletion (F:SimpleGraph V)
    (s₁ s₂:Finset I) (hs:Disjoint s₁ s₂)
    (u v:I→V) (P:∀i,F.Walk (u i) (v i))
    (hp:∀i∈s₁∪s₂,(P i).IsPath)
    (hP:(↑(s₁∪s₂):Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset))
    (c d:ℕ) (hc:0<c) (hlen:∀i∈s₁∪s₂,(P i).length=c*d+4)
    (T:I→Finset ℕ) (hT:∀i,T i⊆Finset.range d) (C:Finset V)
    (hC:∀i∈s₁∪s₂,Disjoint (P i).support.toFinset C)
    (i:I) (hi:i∈s₂) (j:ℕ) (hj:j≤d):
    (P i).getVert (2+c*j)∉C ∪ (s₁∪s₂).biUnion (pathFamilyLocalDeletion F s₁ u v P c d T hT) ↔
      j∈survivingSegmentMarkers d (T i) := by
  have hi':i∈s₁∪s₂:=Finset.mem_union_right _ hi
  have hinot:i∉s₁ := by intro h;exact Finset.disjoint_left.mp hs h hi
  have hD:∀k∈s₁∪s₂,pathFamilyLocalDeletion F s₁ u v P c d T hT k⊆(P k).support.toFinset := by
    intro k hk
    exact path_family_local_deletion_subset F s₁ u v P c d T hT k (hlen k hk)
  have hx:(P i).getVert (2+c*j)∈(P i).support.toFinset := by simp
  have hloc:=disjoint_family_deletion_localization (s₁∪s₂) (fun k=>(P k).support.toFinset)
    (pathFamilyLocalDeletion F s₁ u v P c d T hT) C hP hD hC i hi' _ hx
  rw [hloc]
  simp only [pathFamilyLocalDeletion,hinot,ite_false]
  exact selected_marker_survival_iff (P i) (hp i hi') c d hc (hlen i hi') (T i) (hT i) j hj
end Oberwolfach
