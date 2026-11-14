module

public import Oberwolfach.OrdinaryCycleCountBounds

@[expose] public section

/-! The actual cycles in an ordinary single-vertex transfer. A configuration
has r squared distinct free labels and one excluded root. Each row supplies
the two cycles obtained by replacing its first vertex by the root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem cycleGraph_support_eq_univ {r : ℕ} (hr : 3≤r) :
    (SimpleGraph.cycleGraph r).support=Set.univ := by
  apply Set.eq_univ_of_forall
  intro i
  by_contra hi
  have hz := ((SimpleGraph.cycleGraph r).degree_eq_zero_iff_notMem_support i).mpr hi
  have hd := cycleGraph_regular hr i
  simp only [← SimpleGraph.ncard_neighborSet] at hz hd
  omega

theorem cycle_map_support {V : Type*} {r : ℕ} (hr : 3≤r) (f : Fin r ↪ V) :
    ((SimpleGraph.cycleGraph r).map f).support=Set.range f := by
  rw [SimpleGraph.support_map,cycleGraph_support_eq_univ hr,Set.image_univ]

def transferBaseEmbedding {V : Type*} {r : ℕ} (hr : 0<r)
    (f : (Fin r × Fin r) ↪ V) : Fin r ↪ V where
  toFun i := f (i,⟨0,hr⟩)
  inj' := by intro i j h;exact congrArg Prod.fst (f.injective h)

def transferRowEmbedding {V : Type*} {r : ℕ}
    (f : (Fin r × Fin r) ↪ V) (i : Fin r) : Fin r ↪ V where
  toFun j := f (i,j)
  inj' := by intro j k h;exact congrArg Prod.snd (f.injective h)

def transferRootedEmbedding {V : Type*} {r : ℕ} (hr : 0<r)
    (f : (Fin r × Fin r) ↪ V) (v : V) (hv : v∉Set.range f) (i : Fin r) : Fin r ↪ V where
  toFun j := if j=⟨0,hr⟩ then v else f (i,j)
  inj' := by
    intro j k h
    by_cases hj : j=⟨0,hr⟩ <;> by_cases hk : k=⟨0,hr⟩
    · exact hj.trans hk.symm
    · simp only [hj,ite_true,hk,ite_false] at h
      exact False.elim (hv ⟨(i,k),h.symm⟩)
    · simp only [hj,ite_false,hk,ite_true] at h
      exact False.elim (hv ⟨(i,j),h⟩)
    · simp only [hj,hk,ite_false] at h
      exact congrArg Prod.snd (f.injective h)

theorem transfer_rooted_range_difference {V : Type*} {r : ℕ} (hr : 0<r)
    (f : (Fin r × Fin r) ↪ V) (v : V) (hv : v∉Set.range f) (i : Fin r) (z : V) :
    (if z∈Set.range (transferRootedEmbedding hr f v hv i) then (1:ℝ) else 0)-
      (if z∈Set.range (transferRowEmbedding f i) then (1:ℝ) else 0)=
      (if z=v then 1 else 0)-(if z=f (i,⟨0,hr⟩) then 1 else 0) := by
  have h0 : f (i,⟨0,hr⟩)≠v := fun h => hv ⟨(i,⟨0,hr⟩),h⟩
  by_cases hzv : z=v
  · subst z
    have hin : v∈Set.range (transferRootedEmbedding hr f v hv i) :=
      ⟨⟨0,hr⟩,by simp [transferRootedEmbedding]⟩
    have hout : v∉Set.range (transferRowEmbedding f i) := by
      rintro ⟨j,hj⟩
      exact hv ⟨(i,j),hj⟩
    simp [hin,hout,h0.symm]
  · by_cases hz0 : z=f (i,⟨0,hr⟩)
    · subst z
      have hin : f (i,⟨0,hr⟩)∈Set.range (transferRowEmbedding f i) := ⟨⟨0,hr⟩,rfl⟩
      have hout : f (i,⟨0,hr⟩)∉Set.range (transferRootedEmbedding hr f v hv i) := by
        rintro ⟨j,hj⟩
        change (if j=⟨0,hr⟩ then v else f (i,j))=f (i,⟨0,hr⟩) at hj
        split_ifs at hj with hj0
        · exact h0 hj.symm
        · exact hj0 (congrArg Prod.snd (f.injective hj))
      simp [hin,hout,h0]
    · have he : z∈Set.range (transferRootedEmbedding hr f v hv i) ↔
          z∈Set.range (transferRowEmbedding f i) := by
        constructor
        · rintro ⟨j,hj⟩
          change (if j=⟨0,hr⟩ then v else f (i,j))=z at hj
          split_ifs at hj with hj0
          · exact False.elim (hzv hj.symm)
          · exact ⟨j,hj⟩
        · rintro ⟨j,hj⟩
          have hj0 : j≠⟨0,hr⟩ := by intro hh;subst j;exact hz0 hj.symm
          exact ⟨j,by simpa only [transferRootedEmbedding,transferRowEmbedding,Function.Embedding.coeFn_mk,if_neg hj0] using hj⟩
      simp only [he,hzv,hz0,ite_false,sub_self]

end Oberwolfach
