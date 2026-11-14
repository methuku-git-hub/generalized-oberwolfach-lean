module

public import Oberwolfach.RawIntervalProtectedUnassignedList
public import Oberwolfach.MarkedPermutationIntervalGeometry

@[expose] public section
/-! Protected unassigned lists avoid every retained final-path root interval. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_protected_list_disjoint_retained_roots
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (hd:1≤d)
    (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ false) t) (u:U):
    Disjoint (rawIntervalProtectedUnassignedList π d σ false true t J u)
      (markedIntervalRootSet π (fun _:retainedMarkedIndex π d σ false t J u=>d) Subtype.val):=by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i,hi,hy⟩:=Finset.mem_biUnion.mp hy
  obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hy
  exact False.elim (by
    have hnot: (π^j.val) i.val ∉ rawIntervalProtectedUnassignedList π d σ false true t J u := by
      simpa [retainedAndRawIntervalRoot] using (raw_interval_protected_unassigned_avoids_labels π d hd σ false true t J u false).2 (.inl i) j.castSucc
    exact hnot hx)
end Oberwolfach
