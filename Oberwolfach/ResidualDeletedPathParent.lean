module

public import Oberwolfach.ResidualDeletedPathProperties

@[expose] public section
/-! Every deleted path is contained in its own extended source path. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

def deletedPathParent {s₁ s₂:Finset I} {d:ℕ} {T:I→Finset ℕ}:
    DeletedPathIndex s₁ s₂ d T→I
  | .inl i => i.1
  | .inr ⟨i,_⟩ => i.1

theorem deleted_path_parent_mem {s₁ s₂:Finset I} {d:ℕ} {T:I→Finset ℕ}
    (z:DeletedPathIndex s₁ s₂ d T):deletedPathParent z∈s₁∪s₂ := by
  cases z with
  | inl i => exact Finset.mem_union_left _ i.2
  | inr z => exact Finset.mem_union_right _ z.1.2

theorem walk_interval_support_subset {F:SimpleGraph V} {u v:V} (p:F.Walk u v)
    (a b:ℕ) (hab:a≤b) (hb:b≤p.length):
    (walkInterval p a b hab).support.toFinset⊆p.support.toFinset := by
  intro x hx
  obtain ⟨j,_,_,hj⟩:=(walk_interval_mem_support_iff p a b hab hb x).mp (List.mem_toFinset.mp hx)
  rw [←hj]
  exact List.mem_toFinset.mpr (p.getVert_mem_support j)

theorem deleted_path_support_subset_parent (F:SimpleGraph V)
    (s₁ s₂:Finset I) (u v:I→V) (P:∀i,F.Walk (u i) (v i))
    (c d:ℕ) (hlen:∀i∈s₁∪s₂,(P i).length=c*d+4)
    (T:I→Finset ℕ) (hT:∀i∈s₂,T i⊆Finset.range d)
    (z:DeletedPathIndex s₁ s₂ d T):
    (deletedPathWalk F s₁ s₂ u v P c d T hT z).support.toFinset⊆
      (P (deletedPathParent z)).support.toFinset := by
  cases z with
  | inl i =>
    have hright:2+c*d≤(P i.1).length := by rw [hlen i.1 (Finset.mem_union_left _ i.2)];omega
    exact walk_interval_support_subset (P i.1) 2 (2+c*d) (by omega) hright
  | inr z =>
    rcases z with ⟨i,r⟩
    rcases r with ⟨⟨a,b⟩,hr⟩
    have hr':IsSelectedSegmentRun (T i.1) a b := (selected_run_mem d (T i.1) (hT i.1 i.2) a b).mp hr
    have hbT:b∈T i.1:=hr'.2.1 b hr'.1 le_rfl
    have hbd:b<d:=by have hh:=hT i.1 i.2 hbT;simpa using hh
    have hright:2+c*(b+1)≤(P i.1).length := by
      have hh:=Nat.mul_le_mul_left c (show b+1≤d by omega)
      rw [hlen i.1 (Finset.mem_union_right _ i.2)];omega
    exact walk_interval_support_subset (P i.1) (2+c*a) (2+c*(b+1)) (by
      have hh:=Nat.mul_le_mul_left c (show a≤b+1 by have z:=hr'.1;omega);omega) hright
end Oberwolfach
