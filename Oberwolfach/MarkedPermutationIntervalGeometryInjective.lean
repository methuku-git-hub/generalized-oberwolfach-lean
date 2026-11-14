module

public import Oberwolfach.MarkedPermutationIntervalGeometry

@[expose] public section
/-! Turn pairwise disjoint extended permutation intervals into the finite
indexed interval data used by marked-wheel reconstruction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def markedOrbitIntervalEmbeddingOfInjective {V:Type*} (π:Equiv.Perm V) (k:ℕ) (a:V)
    (hinj:Function.Injective (fun i:Fin (k+1)=>(π^i.val) a)):Fin (k+1)↪V :=
  ⟨fun i=>(π^i.val) a,hinj⟩

theorem marked_permutation_interval_geometry_of_injective
    {V I:Type*} [Fintype V] [Fintype I] [DecidableEq V]
    (π:Equiv.Perm V) (k:I→ℕ) (a:I→V) (S:Finset V)
    (hinj:∀j,Function.Injective (fun i:Fin (k j+1)=>(π^i.val) (a j)))
    (hdis:∀j l:I,j≠l→Disjoint (permutationWindow π 0 (k j) (a j))
      (permutationWindow π 0 (k l) (a l)))
    (hend:∀j,(π^(k j)) (a j)∉S):
    let Y:=markedIntervalRootSet π k a
    ∃v:∀j:I,Fin (k j+1)↪V,
      (∀j,v j 0=a j) ∧ (∀j,v j (Fin.last (k j))=(π^(k j)) (a j)) ∧
      (∀j (i:Fin (k j)),v j i.castSucc∈Y) ∧
      (∀j (i:Fin (k j)),π (v j i.castSucc)=v j i.succ) ∧
      (∀j,v j (Fin.last (k j))∉S) ∧
      (∀j l:I,j≠l→∀i:Fin (k j),∀t:Fin (k l),v j i.castSucc≠v l t.castSucc) ∧
      (∀x∈Y,∃j:I,∃i:Fin (k j),v j i.castSucc=x) ∧
      (∀j l:I,j≠l→v j (Fin.last (k j))≠v l (Fin.last (k l))) := by
  let Y:=markedIntervalRootSet π k a
  let v:∀j:I,Fin (k j+1)↪V:=fun j=>markedOrbitIntervalEmbeddingOfInjective π (k j) (a j) (hinj j)
  have hwindow:∀j (i:Fin (k j+1)),v j i∈permutationWindow π 0 (k j) (a j):=by
    intro j i
    unfold permutationWindow
    apply Finset.mem_image.mpr
    exact ⟨⟨i.val,by omega⟩,Finset.mem_univ _,by simp [v,markedOrbitIntervalEmbeddingOfInjective];rfl⟩
  refine ⟨v,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro j; simp [v,markedOrbitIntervalEmbeddingOfInjective]
  · intro j; rfl
  · intro j i
    apply Finset.mem_biUnion.mpr
    refine ⟨j,Finset.mem_univ _,?_⟩
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  · intro j i
    change π ((π^i.val) (a j))=(π^(i.val+1)) (a j)
    rw [pow_succ',Equiv.Perm.mul_apply]
  · intro j
    exact hend j
  · intro j l hjl i t heq
    exact Finset.disjoint_left.mp (hdis j l hjl) (hwindow j i.castSucc) (heq ▸ hwindow l t.castSucc)
  · intro x hx
    obtain ⟨j,_,hxj⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hxj
    exact ⟨j,i,hi⟩
  · intro j l hjl heq
    exact Finset.disjoint_left.mp (hdis j l hjl) (hwindow j (Fin.last (k j))) (heq ▸ hwindow l (Fin.last (k l)))
end Oberwolfach
