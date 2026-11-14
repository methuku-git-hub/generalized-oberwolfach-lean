module

public import Oberwolfach.BufferedCanonicalOrientedArcs
public import Oberwolfach.FactorCycleOrientationEdges

@[expose] public section
/-! Every canonical arc follows the directed embedding of the same
complement factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_canonical_arcs_from_directed_complement
    {X V I:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V] [Fintype I]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (e:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪X) (inner:∀i,Fin (n i+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (hσ:(complementTailDomain (bufferedPathFullDomain n inner) (bufferedFinalEndpoints n inner)).image
      (factorCycleOrientation G e)=complementTailDomain (bufferedPathFullDomain n inner) (bufferedInitialEndpoints n inner))
    (fC:{x // x∉bufferedPathStrictInterior n inner}↪V) (Dsrc:X→X→Prop)
    (horient:∀x,Dsrc x (factorCycleOrientation G e x)) (Dhost:V→V→Prop)
    (hDir:∀x y:{x // x∉bufferedPathStrictInterior n inner},G.Adj x.1 y.1→Dsrc x.1 y.1→Dhost (fC x) (fC y)):
    let tail:=bufferedOrientedTailEmbedding n ext inner hinner hdis fC
    let head:=bufferedOrientedHeadEmbedding n ext inner hinner hdis (factorCycleOrientation G e) hσ fC
    ∀z,Dhost (tail z) (head z):=by
  let A:=bufferedPathFullDomain n inner
  let D:=bufferedPathStrictInterior n inner
  let B:=bufferedFinalEndpoints n inner
  let T:=bufferedInitialEndpoints n inner
  let σ:=factorCycleOrientation G e
  let hDA:D⊆A:=buffered_strict_interior_subset_domain n inner
  let hBD:Disjoint B D:=buffered_final_endpoints_disjoint_strict n ext inner hinner hdis
  let hTD:Disjoint T D:=buffered_initial_endpoints_disjoint_strict n ext inner hinner hdis
  intro tail head z
  have hx:z.val∉D:=by
    intro hd
    rcases Finset.mem_union.mp z.property with hout|hb
    · exact (Finset.mem_sdiff.mp hout).2 (hDA hd)
    · exact Finset.disjoint_left.mp hBD hb hd
  have hy:σ z.val∉D:=by
    have hh:σ z.val∈complementTailDomain A T:=by
      rw [←hσ]
      exact Finset.mem_image.mpr ⟨z.val,z.property,rfl⟩
    intro hd
    rcases Finset.mem_union.mp hh with hout|ht
    · exact (Finset.mem_sdiff.mp hout).2 (hDA hd)
    · exact Finset.disjoint_left.mp hTD ht hd
  change Dhost (fC ⟨z.val,hx⟩) (fC ⟨σ z.val,hy⟩)
  exact hDir ⟨z.val,hx⟩ ⟨σ z.val,hy⟩ (factor_cycle_orientation_adj G hG e z.val) (horient z.val)

theorem buffered_canonical_arc_physically_in_complement
    {X V I:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V] [Fintype I]
    (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (e:∀C:G.ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪X) (inner:∀i,Fin (n i+1)↪X)
    (hinner:∀i p,inner i p=ext i ⟨p.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (hσ:(complementTailDomain (bufferedPathFullDomain n inner) (bufferedFinalEndpoints n inner)).image
      (factorCycleOrientation G e)=complementTailDomain (bufferedPathFullDomain n inner) (bufferedInitialEndpoints n inner))
    (fC:{x // x∉bufferedPathStrictInterior n inner}↪V):
    let tail:=bufferedOrientedTailEmbedding n ext inner hinner hdis fC
    let head:=bufferedOrientedHeadEmbedding n ext inner hinner hdis (factorCycleOrientation G e) hσ fC
    ∀z,s(tail z,head z)∈((G.induce {x | x∉bufferedPathStrictInterior n inner}).edgeFinset.image (Sym2.map fC)):=by
  let A:=bufferedPathFullDomain n inner
  let D:=bufferedPathStrictInterior n inner
  let B:=bufferedFinalEndpoints n inner
  let T:=bufferedInitialEndpoints n inner
  let σ:=factorCycleOrientation G e
  let hDA:D⊆A:=buffered_strict_interior_subset_domain n inner
  let hBD:Disjoint B D:=buffered_final_endpoints_disjoint_strict n ext inner hinner hdis
  let hTD:Disjoint T D:=buffered_initial_endpoints_disjoint_strict n ext inner hinner hdis
  intro tail head z
  have hx:z.val∉D:=by
    intro hd
    rcases Finset.mem_union.mp z.property with hout|hb
    · exact (Finset.mem_sdiff.mp hout).2 (hDA hd)
    · exact Finset.disjoint_left.mp hBD hb hd
  have hy:σ z.val∉D:=by
    have hh:σ z.val∈complementTailDomain A T:=by
      rw [←hσ]
      exact Finset.mem_image.mpr ⟨z.val,z.property,rfl⟩
    intro hd
    rcases Finset.mem_union.mp hh with hout|ht
    · exact (Finset.mem_sdiff.mp hout).2 (hDA hd)
    · exact Finset.disjoint_left.mp hTD ht hd
  change s(fC ⟨z.val,hx⟩,fC ⟨σ z.val,hy⟩)∈_
  apply Finset.mem_image.mpr
  refine ⟨s(⟨z.val,hx⟩,⟨σ z.val,hy⟩),?_,by simp⟩
  exact SimpleGraph.mem_edgeFinset.mpr (factor_cycle_orientation_adj G hG e z.val)

theorem buffered_canonical_arcs_disjoint_from_complement_packing
    {V W:Type} [Fintype V] [DecidableEq V] [Fintype W]
    {I X:W→Type} [∀w,Fintype (I w)] [∀w,Fintype (X w)] [∀w,DecidableEq (X w)]
    (G:∀w,SimpleGraph (X w)) (hG:∀w,(G w).IsRegularOfDegree 2)
    (e:∀w,∀C:(G w).ConnectedComponent,SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (n:∀w,I w→ℕ) (ext:∀w i,Fin (n w i+5)↪X w) (inner:∀w i,Fin (n w i+1)↪X w)
    (hinner:∀w i p,inner w i p=ext w i ⟨p.val+2,by omega⟩)
    (hdis:∀w i j,i≠j→Disjoint (Finset.univ.image (ext w i)) (Finset.univ.image (ext w j)))
    (hσ:∀w,(complementTailDomain (bufferedPathFullDomain (n w) (inner w)) (bufferedFinalEndpoints (n w) (inner w))).image
      (factorCycleOrientation (G w) (e w))=complementTailDomain (bufferedPathFullDomain (n w) (inner w)) (bufferedInitialEndpoints (n w) (inner w)))
    (fC:∀w,{x // x∉bufferedPathStrictInterior (n w) (inner w)}↪V)
    (hpack:∀w z,w≠z→Disjoint
      (((G w).induce {x | x∉bufferedPathStrictInterior (n w) (inner w)}).edgeFinset.image (Sym2.map (fC w)))
      (((G z).induce {x | x∉bufferedPathStrictInterior (n z) (inner z)}).edgeFinset.image (Sym2.map (fC z)))):
    let tail:=fun w=>bufferedOrientedTailEmbedding (n w) (ext w) (inner w) (hinner w) (hdis w) (fC w)
    let head:=fun w=>bufferedOrientedHeadEmbedding (n w) (ext w) (inner w) (hinner w) (hdis w)
      (factorCycleOrientation (G w) (e w)) (hσ w) (fC w)
    ∀w z,w≠z→Disjoint (Finset.univ.image (fun x=>(tail w x,head w x)))
      (Finset.univ.image (fun x=>(tail z x,head z x))):=by
  intro tail head w z hwz
  apply Finset.disjoint_left.mpr
  intro arc ha hb
  obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp ha
  obtain ⟨b,_,heq⟩:=Finset.mem_image.mp hb
  have ha':=buffered_canonical_arc_physically_in_complement (G w) (hG w) (e w)
    (n w) (ext w) (inner w) (hinner w) (hdis w) (hσ w) (fC w) a
  have hb':=buffered_canonical_arc_physically_in_complement (G z) (hG z) (e z)
    (n z) (ext z) (inner z) (hinner z) (hdis z) (hσ z) (fC z) b
  have heq':s(tail z b,head z b)=s(tail w a,head w a):=congrArg (fun p:V×V=>s(p.1,p.2)) heq
  exact (Finset.disjoint_left.mp (hpack w z hwz)) ha' (heq' ▸ hb')

end Oberwolfach
