module

public import Oberwolfach.MarkedPermutationIntervalGeometryInjective

@[expose] public section
/-! Exact cardinality of the selected marked interval root set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_interval_root_card
    {V I:Type*} [Fintype V] [Fintype I] [DecidableEq V]
    (π:Equiv.Perm V) (k:I→ℕ) (a:I→V)
    (hinj:∀j,Function.Injective (fun i:Fin (k j+1)=>(π^i.val) (a j)))
    (hdis:∀j l:I,j≠l→Disjoint (permutationWindow π 0 (k j) (a j))
      (permutationWindow π 0 (k l) (a l))):
    (markedIntervalRootSet π k a).card=∑j,k j:=by
  classical
  have hsub (j:I):Finset.univ.image (fun i:Fin (k j)=>(π^i.val) (a j))⊆
      permutationWindow π 0 (k j) (a j):=by
    intro x hx
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
    unfold permutationWindow
    apply Finset.mem_image.mpr
    exact ⟨⟨i.val,by omega⟩,Finset.mem_univ _,by simp; rfl⟩
  have hinj' (j:I):Function.Injective (fun i:Fin (k j)=>(π^i.val) (a j)):=by
    intro x y h
    apply Fin.castSucc_injective
    apply hinj j
    exact h
  unfold markedIntervalRootSet
  rw [Finset.card_biUnion (by
    intro j hj l hl hjl
    exact (hdis j l hjl).mono (hsub j) (hsub l))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.card_image_of_injective _ (hinj' j),Finset.card_univ,Fintype.card_fin]

theorem marked_uniform_interval_root_card
    {V I:Type*} [Fintype V] [Fintype I] [DecidableEq V]
    (π:Equiv.Perm V) (d:ℕ) (a:I→V)
    (hinj:∀j,Function.Injective (fun i:Fin (d+1)=>(π^i.val) (a j)))
    (hdis:∀j l:I,j≠l→Disjoint (permutationWindow π 0 d (a j))
      (permutationWindow π 0 d (a l))):
    (markedIntervalRootSet π (fun _=>d) a).card=Fintype.card I*d:=by
  simpa using marked_interval_root_card π (fun _=>d) a hinj hdis
end Oberwolfach
