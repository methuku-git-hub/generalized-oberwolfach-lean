module

public import Oberwolfach.BufferedOrientedPathOrbit
public import Oberwolfach.PermutationBoundaryComplement
public import Oberwolfach.BufferedFinalEndpointGeometry

@[expose] public section
/-! The factor orientation maps unused source tails to unused source heads. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_oriented_source_complement
    {X I:Type*} [Fintype X] [DecidableEq X] [Fintype I]
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪X) (inner:∀i,Fin (n i+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (σ:Equiv.Perm X) (hn:∀i,0<n i)
    (hstep:∀i (p:Fin (n i)),σ (inner i p.castSucc)=inner i p.succ):
    ((Finset.univ\bufferedPathFullDomain n inner)∪bufferedFinalEndpoints n inner).image σ =
      (Finset.univ\bufferedPathFullDomain n inner)∪(Finset.univ.image (fun i=>inner i 0)):=by
  classical
  let a:I→X:=fun i=>inner i 0
  let Y:=markedIntervalRootSet σ n a
  let B:=bufferedFinalEndpoints n inner
  let T:=Finset.univ.image a
  let A:=bufferedPathFullDomain n inner
  have horbit:=buffered_path_follows_permutation n inner σ hstep
  have hinj:∀i,Function.Injective (fun p:Fin (n i+1)=>(σ^p.val) (a i)):=by
    intro i p q he
    apply (inner i).injective
    simpa only [a,←horbit i p,←horbit i q] using he
  have hwin (i:I):permutationWindow σ 0 (n i) (a i)=Finset.univ.image (inner i):=by
    unfold permutationWindow
    have hh:(σ^0).symm (a i)=a i:=by rfl
    simp only [hh]
    ext x
    constructor
    · intro hx
      obtain ⟨p,_,hp⟩:=Finset.mem_image.mp hx
      let q:Fin (n i+1):=⟨p.val,by omega⟩
      refine Finset.mem_image.mpr ⟨q,Finset.mem_univ _,?_⟩
      exact (horbit i q).trans hp
    · intro hx
      obtain ⟨p,_,hp⟩:=Finset.mem_image.mp hx
      let q:Fin (0+n i+1):=⟨p.val,by omega⟩
      refine Finset.mem_image.mpr ⟨q,Finset.mem_univ _,?_⟩
      exact (horbit i p).symm.trans hp
  have hwindows:∀i j:I,i≠j→Disjoint (permutationWindow σ 0 (n i) (a i))
      (permutationWindow σ 0 (n j) (a j)):=by
    intro i j hij
    rw [hwin i,hwin j]
    exact buffered_inner_domains_disjoint n ext inner hinner hdis i j hij
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
  have hshift:Y∪B=Y.image σ∪T:=buffered_oriented_path_boundary_identity n inner σ hn hstep
  have hB:B=Finset.univ.image (fun i=>(σ^(n i)) (a i)):=by
    apply Finset.image_congr
    intro i hi
    exact horbit i (Fin.last (n i))
  have hYB:Disjoint Y B:=by
    rw [hB]
    exact marked_interval_roots_disjoint_endpoints σ n a hinj hwindows
  have hYT:Disjoint (Y.image σ) T:=marked_shifted_roots_disjoint_starts σ n a hinj hwindows
  exact permutation_maps_path_complement σ A Y B T hA hshift hYB hYT
end Oberwolfach
