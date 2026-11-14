module

public import Oberwolfach.MarkedPermutationIntervalGeometryInjective

@[expose] public section
/-! Distinct final intervals separate their marked roots and finish points. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_interval_roots_disjoint_endpoints
    {V I:Type*} [Fintype V] [Fintype I] [DecidableEq V]
    (π:Equiv.Perm V) (k:I→ℕ) (a:I→V)
    (hinj:∀j,Function.Injective (fun i:Fin (k j+1)=>(π^i.val) (a j)))
    (hdis:∀j l:I,j≠l→Disjoint (permutationWindow π 0 (k j) (a j))
      (permutationWindow π 0 (k l) (a l))):
    Disjoint (markedIntervalRootSet π k a)
      (Finset.univ.image (fun j=>(π^(k j)) (a j))):=by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp hx
  obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hj
  obtain ⟨l,_,hl⟩:=Finset.mem_image.mp hy
  have hroot:(π^i.val) (a j)∈permutationWindow π 0 (k j) (a j):=by
    unfold permutationWindow
    exact Finset.mem_image.mpr ⟨⟨i.val,by omega⟩,Finset.mem_univ _,by simp; rfl⟩
  have hend:(π^(k l)) (a l)∈permutationWindow π 0 (k l) (a l):=by
    unfold permutationWindow
    exact Finset.mem_image.mpr ⟨⟨k l,by omega⟩,Finset.mem_univ _,by simp; rfl⟩
  by_cases hjl:j=l
  · subst l
    have heq:(π^i.castSucc.val) (a j)=(π^(Fin.last (k j)).val) (a j):=hi.trans hl.symm
    have he:=hinj j heq
    have hv:=congrArg Fin.val he
    simp only [Fin.val_castSucc,Fin.val_last] at hv
    omega
  · apply Finset.disjoint_left.mp (hdis j l hjl) hroot
    have hv:(π^i.val) (a j)=(π^(k l)) (a l):=hi.trans hl.symm
    exact hv.symm ▸ hend

theorem marked_interval_roots_in_residual
    {V I:Type*} [Fintype V] [Fintype I] [DecidableEq V]
    (π:Equiv.Perm V) (k:I→ℕ) (a:I→V)
    (hinj:∀j,Function.Injective (fun i:Fin (k j+1)=>(π^i.val) (a j)))
    (hdis:∀j l:I,j≠l→Disjoint (permutationWindow π 0 (k j) (a j))
      (permutationWindow π 0 (k l) (a l)))
    (Z R:Finset V)
    (havoid:Disjoint (markedIntervalRootSet π k a) Z)
    (hR:R=Finset.univ\(Z ∪ Finset.univ.image (fun j=>(π^(k j)) (a j)))):
    markedIntervalRootSet π k a⊆R:=by
  intro x hx
  rw [hR]
  simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_union,not_or]
  exact ⟨fun hz=>Finset.disjoint_left.mp havoid hx hz,
    fun hb=>Finset.disjoint_left.mp (marked_interval_roots_disjoint_endpoints π k a hinj hdis) hx hb⟩
end Oberwolfach
