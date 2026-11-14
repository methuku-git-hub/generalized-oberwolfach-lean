module

public import Oberwolfach.ResidualPathIntervalSupport

@[expose] public section
/-! A vertex on a simple path is internal to a subpath exactly when its
index is strictly between the endpoint indices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem path_marker_in_interval_interior_iff {F:SimpleGraph V} {u v:V}
    (p:F.Walk u v) (hp:p.IsPath) (a b j:ℕ) (hab:a≤b)
    (hb:b≤p.length) (hj:j≤p.length):
    p.getVert j∈(walkInterval p a b hab).support.toFinset \ {p.getVert a,p.getVert b} ↔
      a<j ∧ j<b := by
  constructor
  · intro hx
    have hx':=Finset.mem_sdiff.mp hx
    obtain ⟨k,hak,hkb,hk⟩:=(walk_interval_mem_support_iff p a b hab hb _).mp
      (List.mem_toFinset.mp hx'.1)
    have hkj:k=j := hp.getVert_injOn (by simp;omega) (by simpa using hj) hk
    have hnotA:p.getVert j≠p.getVert a := by intro h;apply hx'.2;simp [h]
    have hnotB:p.getVert j≠p.getVert b := by intro h;apply hx'.2;simp [h]
    constructor
    · by_contra h
      have : j=a := by omega
      apply hnotA
      rw [this]
    · by_contra h
      have : j=b := by omega
      apply hnotB
      rw [this]
  · rintro ⟨haj,hjb⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · apply List.mem_toFinset.mpr
      apply (walk_interval_mem_support_iff p a b hab hb _).mpr
      exact ⟨j,by omega,by omega,rfl⟩
    · simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
      constructor
      · intro heq
        have hh:=hp.getVert_injOn (by simpa using hj) (by simp;omega) heq
        omega
      · intro heq
        have hh:=hp.getVert_injOn (by simpa using hj) (by simpa using hb) heq
        omega
end Oberwolfach
