module

public import Oberwolfach.BufferedOrientedSourceComplement
public import Oberwolfach.ComplementOrientedArcImages

@[expose] public section
/-! The complement of the selected path-tail set is exactly the outside-path
vertices together with the final endpoints. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_oriented_tail_domain
    {X I:Type*} [Fintype X] [DecidableEq X] [Fintype I]
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪X) (inner:∀i,Fin (n i+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (σ:Equiv.Perm X)
    (hstep:∀i (p:Fin (n i)),σ (inner i p.castSucc)=inner i p.succ):
    Finset.univ\markedIntervalRootSet σ n (fun i=>inner i 0)=
      complementTailDomain (bufferedPathFullDomain n inner) (bufferedFinalEndpoints n inner):=by
  classical
  let a:I→X:=fun i=>inner i 0
  let Y:=markedIntervalRootSet σ n a
  let B:=bufferedFinalEndpoints n inner
  let A:=bufferedPathFullDomain n inner
  have horbit:=buffered_path_follows_permutation n inner σ hstep
  have hA:Y∪B=A:=by
    apply Finset.Subset.antisymm
    · intro x hx
      rcases Finset.mem_union.mp hx with hy | hb
      · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hy
        obtain ⟨p,_,rfl⟩:=Finset.mem_image.mp hi
        apply Finset.mem_biUnion.mpr
        refine ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨p.castSucc,Finset.mem_univ _,?_⟩⟩
        exact horbit i p.castSucc
      · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hb
        exact buffered_path_vertex_mem_domain n inner i (Fin.last (n i))
    · intro x hx
      obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hx
      obtain ⟨p,_,rfl⟩:=Finset.mem_image.mp hi
      by_cases hp:p.val=n i
      · apply Finset.mem_union_right
        have hp':p=Fin.last (n i):=Fin.ext hp
        exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,congrArg (inner i) hp'.symm⟩
      · apply Finset.mem_union_left
        let q:Fin (n i):=⟨p.val,by omega⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨q,Finset.mem_univ _,?_⟩⟩
        exact (horbit i p).symm
  have hYB:Disjoint Y B:=by
    apply Finset.disjoint_left.mpr
    intro x hx hb
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hx
    obtain ⟨p,_,hp⟩:=Finset.mem_image.mp hi
    obtain ⟨j,_,hj⟩:=Finset.mem_image.mp hb
    have hpi:inner i p.castSucc=x:=(horbit i p.castSucc).trans hp
    by_cases hij:i=j
    · subst j
      have he:(p.castSucc:Fin (n i+1))=Fin.last (n i):=(inner i).injective (hpi.trans hj.symm)
      have hv:=congrArg Fin.val he
      simp only [Fin.val_castSucc,Fin.val_last] at hv
      omega
    · have hxI:inner i p.castSucc∈Finset.univ.image (inner i):=Finset.mem_image.mpr ⟨p.castSucc,Finset.mem_univ _,rfl⟩
      have hxJ:inner i p.castSucc∈Finset.univ.image (inner j):=Finset.mem_image.mpr ⟨Fin.last (n j),Finset.mem_univ _,hj.trans hpi.symm⟩
      exact Finset.disjoint_left.mp (buffered_inner_domains_disjoint n ext inner hinner hdis i j hij) hxI hxJ
  change Finset.univ\Y=(Finset.univ\A)∪B
  ext x
  simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.mem_union]
  have hx:x∈A↔x∈Y∨x∈B:=by rw [←hA,Finset.mem_union]
  have hd:¬(x∈Y∧x∈B):=fun h=>Finset.disjoint_left.mp hYB h.1 h.2
  tauto
end Oberwolfach
