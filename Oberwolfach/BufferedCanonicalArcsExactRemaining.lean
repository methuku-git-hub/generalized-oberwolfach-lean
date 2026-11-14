module

public import Oberwolfach.BufferedCanonicalArcsFromRemainingEdges

@[expose] public section
/-! The canonical arcs enumerate every edge of the same complement embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_canonical_arcs_exact_remaining
    {X V I:Type*} [Fintype X] [DecidableEq X] [DecidableEq V] [Fintype I]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (e:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪X) (inner:∀i,Fin (n i+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (hstep:∀i (p:Fin (n i)),factorCycleOrientation G e (inner i p.castSucc)=inner i p.succ)
    (p:∀i,G.Walk (inner i 0) (inner i (Fin.last (n i))))
    (hlen:∀i,(p i).length=n i) (hsupp:∀i,(p i).support=List.ofFn (inner i))
    (hσ:(complementTailDomain (bufferedPathFullDomain n inner) (bufferedFinalEndpoints n inner)).image
      (factorCycleOrientation G e)=complementTailDomain (bufferedPathFullDomain n inner) (bufferedInitialEndpoints n inner))
    (fC:{x // x∉bufferedPathStrictInterior n inner}↪V):
    let tail:=bufferedOrientedTailEmbedding n ext inner hinner hdis fC
    let head:=bufferedOrientedHeadEmbedding n ext inner hinner hdis (factorCycleOrientation G e) hσ fC
    let R:=G.deleteEdges (↑(Finset.univ.biUnion (fun i=>(p i).edges.toFinset)):Set (Sym2 X))
    (Finset.univ.image (fun z=>s(tail z,head z)))=
      ((R.induce {x | x∉bufferedPathStrictInterior n inner}).edgeFinset).image (Sym2.map fC):=by
  intro tail head R
  apply Finset.Subset.antisymm
  · exact buffered_canonical_arcs_in_remaining_edge_image G hG e n ext inner hinner hdis hstep p hlen hsupp hσ fC
  · intro a ha
    obtain ⟨edge,hedge,rfl⟩:=Finset.mem_image.mp ha
    induction edge using Sym2.ind with
    | _ x y =>
      have hadj:R.Adj x.val y.val:=SimpleGraph.mem_edgeFinset.mp hedge
      have hm:s(x.val,y.val)∈G.edgeFinset\(Finset.univ.biUnion (fun i=>(p i).edges.toFinset)):=by
        rw [←SimpleGraph.edgeFinset_deleteEdges]
        exact SimpleGraph.mem_edgeFinset.mpr hadj
      rw [buffered_factor_remaining_edges G hG e n ext inner hinner hdis hstep p hlen hsupp] at hm
      obtain ⟨z,hz,hze⟩:=Finset.mem_image.mp hm
      have hzD:z∉bufferedPathStrictInterior n inner:=by
        intro hzD
        have hh:=buffered_strict_interior_subset_domain n inner hzD
        rcases Finset.mem_union.mp hz with ho|hb
        · exact (Finset.mem_sdiff.mp ho).2 hh
        · exact Finset.disjoint_left.mp (buffered_final_endpoints_disjoint_strict n ext inner hinner hdis) hb hzD
      have hσD:factorCycleOrientation G e z∉bufferedPathStrictInterior n inner:=by
        have hh:factorCycleOrientation G e z∈complementTailDomain (bufferedPathFullDomain n inner) (bufferedInitialEndpoints n inner):=by
          rw [←hσ]
          exact Finset.mem_image.mpr ⟨z,hz,rfl⟩
        intro hD
        rcases Finset.mem_union.mp hh with ho|ht
        · exact (Finset.mem_sdiff.mp ho).2 (buffered_strict_interior_subset_domain n inner hD)
        · exact Finset.disjoint_left.mp (buffered_initial_endpoints_disjoint_strict n ext inner hinner hdis) ht hD
      refine Finset.mem_image.mpr ⟨⟨z,hz⟩,Finset.mem_univ _,?_⟩
      change s(fC ⟨z,hzD⟩,fC ⟨factorCycleOrientation G e z,hσD⟩)=Sym2.map fC s(x,y)
      have hh: s(⟨z,hzD⟩,⟨factorCycleOrientation G e z,hσD⟩)=s(x,y):=by
        have hh : s(z,factorCycleOrientation G e z)=s(x.val,y.val):=by
          simpa [factorOrientedPhysicalEdge] using hze
        rcases Sym2.eq_iff.mp hh with ⟨h1,h2⟩|⟨h1,h2⟩
        · exact congrArg₂ (fun a b=>s(a,b)) (Subtype.ext h1) (Subtype.ext h2)
        · rw [Sym2.eq_swap]
          exact congrArg₂ (fun a b=>s(a,b)) (Subtype.ext h2) (Subtype.ext h1)
      rw [←hh]
      rfl
end Oberwolfach
