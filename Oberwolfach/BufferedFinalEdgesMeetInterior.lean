module

public import Oberwolfach.BufferedPathInteriorCompletion
public import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal

@[expose] public section
/-! Every edge of a nontrivial reserved path meets its strict interior. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_final_edges_meet_strict_interior
    {X I:Type} [Fintype X] [DecidableEq X] [Fintype I]
    (G:SimpleGraph X) (n:I→ℕ) (inner:∀i,Fin (n i+1)↪X)
    (u v:I→X) (p:∀i,G.Walk (u i) (v i))
    (hsize:∀i,2≤n i) (hsupport:∀i,(p i).support=List.ofFn (inner i)):
    ∀e∈Finset.univ.biUnion (fun i=>(p i).edges.toFinset),
      ∃x∈e.toFinset,x∈bufferedPathStrictInterior n inner :=by
  intro e he
  obtain ⟨i,_,he⟩:=Finset.mem_biUnion.mp he
  induction e using Sym2.ind with
  | _ x y =>
    have hlen:(p i).length=n i:=by
      have hh:=congrArg List.length (hsupport i)
      simp only [SimpleGraph.Walk.length_support,List.length_ofFn] at hh
      omega
    have hmem:s(x,y)∈(p i).edges:=by simpa using he
    obtain ⟨j,hj,hedge⟩:=((p i).mk_mem_edges_iff_exists).mp hmem
    have hjn:j<n i:=by simpa [hlen] using hj
    have hq:∀k:ℕ,(hk:k≤n i)→(p i).getVert k=inner i ⟨k,by omega⟩:=by
      intro k hk
      have hh:some ((p i).getVert k)=(p i).support[k]? :=
        (p i).getVert_eq_support_getElem? (by simpa [hlen] using hk)
      rw [hsupport i] at hh
      simpa only [List.getElem?_ofFn,dif_pos (show k<n i+1 by omega),Option.some.injEq] using hh
    by_cases hj0:j=0
    · let q:Fin (n i+1):=⟨j+1,by omega⟩
      refine ⟨inner i q,?_,?_⟩
      · have hv:(p i).getVert (j+1)∈s(x,y).toFinset:=by rw [←hedge];simp
        simpa only [hq (j+1) (by omega)] using hv
      · apply Finset.mem_biUnion.mpr
        refine ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨q,?_,rfl⟩⟩
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,q]
        have :=hsize i
        omega
    · let q:Fin (n i+1):=⟨j,by omega⟩
      refine ⟨inner i q,?_,?_⟩
      · have hv:(p i).getVert j∈s(x,y).toFinset:=by rw [←hedge];simp
        simpa only [hq j (by omega)] using hv
      · apply Finset.mem_biUnion.mpr
        refine ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨q,?_,rfl⟩⟩
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,q]
        omega
end Oberwolfach
