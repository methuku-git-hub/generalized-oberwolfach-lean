module

public import Oberwolfach.ResidualDeletedPathFamily

@[expose] public section
/-! The indexed deletions are nontrivial simple paths with the prescribed
endpoints. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem deleted_path_family_properties (F:SimpleGraph V)
    (s₁ s₂:Finset I) (u v:I→V) (P:∀i,F.Walk (u i) (v i))
    (hp:∀i∈s₁∪s₂,(P i).IsPath) (c d:ℕ) (hc:0<c) (hd:0<d)
    (hlen:∀i∈s₁∪s₂,(P i).length=c*d+4)
    (T:I→Finset ℕ) (hT:∀i∈s₂,T i⊆Finset.range d):
    ∀ z:DeletedPathIndex s₁ s₂ d T,
      (deletedPathWalk F s₁ s₂ u v P c d T hT z).IsPath ∧
      deletedPathStart F s₁ s₂ u v P c d T z ≠ deletedPathEnd F s₁ s₂ u v P c d T z := by
  intro z
  cases z with
  | inl i =>
    have hi:i.1∈s₁∪s₂:=Finset.mem_union_left _ i.2
    have hright:2+c*d≤(P i.1).length := by rw [hlen i.1 hi];omega
    have hleft:2<2+c*d := by have hh:=Nat.mul_pos hc hd;omega
    exact ⟨walk_interval_isPath (P i.1) (hp i.1 hi) _ _ (by omega),
      path_interval_endpoints_ne (P i.1) (hp i.1 hi) _ _ hleft hright⟩
  | inr z =>
    rcases z with ⟨i,r⟩
    rcases r with ⟨⟨a,b⟩,hr⟩
    have hi:i.1∈s₁∪s₂:=Finset.mem_union_right _ i.2
    have hr':IsSelectedSegmentRun (T i.1) a b := (selected_run_mem d (T i.1) (hT i.1 i.2) a b).mp hr
    have hbT:b∈T i.1:=hr'.2.1 b hr'.1 le_rfl
    have hbd:b<d:=by have hh:=hT i.1 i.2 hbT;simpa using hh
    have hh:=selected_run_walk_properties (P i.1) (hp i.1 hi) c d a b hc hr'.1 hbd (hlen i.1 hi)
    exact ⟨hh.1,hh.2.2.1⟩
end Oberwolfach
