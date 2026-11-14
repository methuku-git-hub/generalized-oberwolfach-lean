module

public import Oberwolfach.MarkedIntervalSuccessorSeparation
public import Oberwolfach.MarkedIntervalEndpointSeparation

@[expose] public section
/-! The interval boundary identity and disjointness of shifted roots from
interval starts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_interval_boundary_identity
    {V I:Type*} [Fintype V] [Fintype I] [DecidableEq V]
    (π:Equiv.Perm V) (k:I→ℕ) (a:I→V) (hk:∀j,0<k j):
    markedIntervalRootSet π k a ∪ Finset.univ.image (fun j=>(π^(k j)) (a j))=
      (markedIntervalRootSet π k a).image π ∪ Finset.univ.image a:=by
  classical
  have hpow (j:I) (n:ℕ):π ((π^n) (a j))=(π^(n+1)) (a j):=by
    rw [pow_succ',Equiv.Perm.mul_apply]
  have hroot (j:I) (i:Fin (k j)):(π^i.val) (a j)∈markedIntervalRootSet π k a:=by
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  apply Finset.Subset.antisymm
  · intro x hx
    rcases Finset.mem_union.mp hx with hy | hb
    · obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp hy
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hj
      by_cases hi:i.val=0
      · apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨j,Finset.mem_univ _,?_⟩
        simp [hi]
      · apply Finset.mem_union_left
        let q:Fin (k j):=⟨i.val-1,by omega⟩
        refine Finset.mem_image.mpr ⟨(π^q.val) (a j),hroot j q,?_⟩
        have hs:i.val-1+1=i.val:=by omega
        simpa [q,hs] using hpow j (i.val-1)
    · obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hb
      apply Finset.mem_union_left
      let q:Fin (k j):=⟨k j-1,by have:=hk j;omega⟩
      refine Finset.mem_image.mpr ⟨(π^q.val) (a j),hroot j q,?_⟩
      have hs:k j-1+1=k j:=by have:=hk j;omega
      simpa [q,hs] using hpow j (k j-1)
  · intro x hx
    rcases Finset.mem_union.mp hx with hy | ht
    · exact marked_interval_successor_subset π k a hy
    · obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp ht
      apply Finset.mem_union_left
      simpa using hroot j ⟨0,hk j⟩

theorem marked_shifted_roots_disjoint_starts
    {V I:Type*} [Fintype V] [Fintype I] [DecidableEq V]
    (π:Equiv.Perm V) (k:I→ℕ) (a:I→V)
    (hinj:∀j,Function.Injective (fun i:Fin (k j+1)=>(π^i.val) (a j)))
    (hdis:∀j l:I,j≠l→Disjoint (permutationWindow π 0 (k j) (a j))
      (permutationWindow π 0 (k l) (a l))):
    Disjoint ((markedIntervalRootSet π k a).image π) (Finset.univ.image a):=by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx ht
  obtain ⟨y,hy,hyx⟩:=Finset.mem_image.mp hx
  obtain ⟨j,_,hj⟩:=Finset.mem_biUnion.mp hy
  obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hj
  obtain ⟨l,_,hl⟩:=Finset.mem_image.mp ht
  have hp:π ((π^i.val) (a j))=(π^(i.val+1)) (a j):=by
    rw [pow_succ',Equiv.Perm.mul_apply]
  have hxj:(π^(i.val+1)) (a j)=x:=by rw [←hp,hi,hyx]
  have hwin:(π^(i.val+1)) (a j)∈permutationWindow π 0 (k j) (a j):=by
    unfold permutationWindow
    exact Finset.mem_image.mpr ⟨⟨i.val+1,by omega⟩,Finset.mem_univ _,by simp; rfl⟩
  have hstart:a l∈permutationWindow π 0 (k l) (a l):=permutationWindow_self π 0 (k l) (a l)
  by_cases hjl:j=l
  · subst l
    have heq:(π^(⟨i.val+1,by omega⟩:Fin (k j+1)).val) (a j)=
        (π^(0:Fin (k j+1)).val) (a j):=by simpa using hxj.trans hl.symm
    have he:=hinj j heq
    have hv:=congrArg Fin.val he
    simp at hv
  · apply Finset.disjoint_left.mp (hdis j l hjl) hwin
    have he:(π^(i.val+1)) (a j)=a l:=hxj.trans hl.symm
    exact he.symm ▸ hstart
end Oberwolfach
