module

public import Oberwolfach.ResidualPathInterval

@[expose] public section
/-! The vertices of a walk interval are exactly those in its index range. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem walk_interval_mem_support_iff {F:SimpleGraph V} {u v:V} (p:F.Walk u v)
    (a b:ℕ) (hab:a≤b) (hb:b≤p.length) (x:V):
    x∈(walkInterval p a b hab).support ↔
      ∃ j,a≤j ∧ j≤b ∧ p.getVert j=x := by
  constructor
  · intro hx
    obtain ⟨k,hk,hkle⟩:=SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
    have hlen:=walk_interval_length p a b hab hb
    have hkle':k≤b-a := by omega
    rw [walk_interval_getVert p a b hab k hkle'] at hk
    exact ⟨a+k,by omega,by omega,hk⟩
  · rintro ⟨j,haj,hjb,hjx⟩
    apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
    refine ⟨j-a,?_,?_⟩
    · rw [walk_interval_getVert p a b hab (j-a) (by omega)]
      simpa [Nat.add_sub_of_le haj] using hjx
    · rw [walk_interval_length p a b hab hb]
      omega

theorem path_interval_endpoints_ne {F:SimpleGraph V} {u v:V} (p:F.Walk u v)
    (hp:p.IsPath) (a b:ℕ) (hab:a<b) (hb:b≤p.length):
    p.getVert a≠p.getVert b := by
  intro heq
  have h:=hp.getVert_injOn (by simp;omega) (by simpa using hb) heq
  omega

theorem disjoint_path_intervals {F:SimpleGraph V} {u v:V} (p:F.Walk u v)
    (hp:p.IsPath) (a b a' b':ℕ) (hab:a≤b) (ha'b':a'≤b')
    (hb':b'≤p.length) (hsep:b<a'):
    Disjoint (walkInterval p a b hab).support.toFinset
      (walkInterval p a' b' ha'b').support.toFinset := by
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  have hb:b≤p.length:=by omega
  obtain ⟨i,hai,hib,hix⟩:=(walk_interval_mem_support_iff p a b hab hb x).mp (List.mem_toFinset.mp hx)
  obtain ⟨j,haj,hjb',hjx⟩:=(walk_interval_mem_support_iff p a' b' ha'b' hb' x).mp (List.mem_toFinset.mp hx')
  have heq:i=j := hp.getVert_injOn (by simp;omega) (by simp;omega) (hix.trans hjx.symm)
  omega
end Oberwolfach
