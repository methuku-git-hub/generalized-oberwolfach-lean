module

public import Oberwolfach.ResidualDeletedIndexFinite

@[expose] public section
/-! Exact lengths of the final paths and the selected-run paths. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem deleted_path_lengths (F:SimpleGraph V) (s₁ s₂:Finset I)
    (u v:I→V) (P:∀i,F.Walk (u i) (v i))
    (hp:∀i∈s₁∪s₂,(P i).IsPath) (c d:ℕ) (hc:0<c)
    (hlen:∀i∈s₁∪s₂,(P i).length=c*d+4)
    (T:I→Finset ℕ) (hT:∀i∈s₂,T i⊆Finset.range d):
    (∀i:{i // i∈s₁},(deletedPathWalk F s₁ s₂ u v P c d T hT (.inl i)).length=c*d) ∧
    (∀i:{i // i∈s₂},∀r:{r // r∈selectedSegmentRuns d (T i.1)},
      (deletedPathWalk F s₁ s₂ u v P c d T hT (.inr ⟨i,r⟩)).length=c*(r.1.2+1-r.1.1)) := by
  constructor
  · intro i
    have hi:i.1∈s₁∪s₂:=Finset.mem_union_left _ i.2
    have hright:2+c*d≤(P i.1).length:=by rw [hlen i.1 hi];omega
    have hh:=walk_interval_length (P i.1) 2 (2+c*d) (by omega) hright
    change (walkInterval (P i.1) 2 (2+c*d) (by omega)).length=c*d
    convert hh using 1 <;> simp
  · intro i r
    have hi:i.1∈s₁∪s₂:=Finset.mem_union_right _ i.2
    have hr: IsSelectedSegmentRun (T i.1) r.1.1 r.1.2 :=
      (selected_run_mem d (T i.1) (hT i.1 i.2) r.1.1 r.1.2).mp r.2
    have hb:r.1.2<d:=by
      have hh:=hT i.1 i.2 (hr.2.1 r.1.2 hr.1 le_rfl)
      simpa using hh
    have hh:=selected_run_walk_properties (P i.1) (hp i.1 hi) c d r.1.1 r.1.2 hc hr.1 hb (hlen i.1 hi)
    exact hh.2.1
end Oberwolfach
