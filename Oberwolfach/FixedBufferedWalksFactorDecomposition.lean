module

public import Oberwolfach.FixedBufferedPathsFromResidualWalks
public import Oberwolfach.MarkedResidualIdentityFactorDecomposition
public import Oberwolfach.SimpleWalkLengthEndpoints
public import Oberwolfach.PhysicalSetFinsetEquivalence

@[expose] public section
/-! Glue residual walks to the complement maps on the fixed buffered source
paths, without replacing the selected factor witnesses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem fixed_buffered_walks_give_factor_decomposition
    {N D:ℕ} (hEven:Even D) (H:SimpleGraph (Fin N)) (hH:H.IsRegularOfDegree D)
    (G:Fin (D/2)→SimpleGraph (Fin N)) (hG:∀u,(G u).IsRegularOfDegree 2)
    (I:Fin (D/2)→Type) [∀u,Fintype (I u)] [∀u,DecidableEq (I u)]
    (Rrim:Finset (Finset (Fin N))) (hRimHost:physicalEdgeGraph Rrim≤H)
    (n:∀u,I u→ℕ)
    (ext:∀u (i:I u),Fin (n u i+5)↪Fin N) (inner:∀u (i:I u),Fin (n u i+1)↪Fin N)
    (hinner:∀u i p,inner u i p=ext u i ⟨p.val+2,by omega⟩)
    (hwalk:∀u i,∃p:(G u).Walk (ext u i 0) (ext u i (Fin.last (n u i+4))),
      p.length=n u i+4 ∧ p.support=List.ofFn (ext u i))
    (hdis:∀u i j,i≠j→Disjoint (Finset.univ.image (ext u i)) (Finset.univ.image (ext u j)))
    (fC:∀u,{x // x∉bufferedPathStrictInterior (n u) (inner u)}↪Fin N)
    (hC:∀u x y,(G u).Adj x.1 y.1→H.Adj (fC u x) (fC u y))
    (start finish:∀u,I u→Fin N)
    (hstart:∀u i (hp:inner u i 0∉bufferedPathStrictInterior (n u) (inner u)),fC u ⟨inner u i 0,hp⟩=start u i)
    (hfinish:∀u i (hp:inner u i (Fin.last (n u i))∉bufferedPathStrictInterior (n u) (inner u)),
      fC u ⟨inner u i (Fin.last (n u i)),hp⟩=finish u i)
    (q:∀u (i:I u),(physicalEdgeGraph Rrim).Walk (start u i) (finish u i))
    (hpath:∀u i,(q u i).IsPath) (hlen:∀u i,(q u i).length=n u i)
    (hwalkDis:∀u i j,i≠j→Disjoint (q u i).support.toFinset (q u j).support.toFinset)
    (hwalkEdge:∀u v,u≠v→∀i:I u,∀j:I v,Disjoint (walkPhysicalEdges (q u i)) (walkPhysicalEdges (q v j)))
    (Rvertex:Fin (D/2)→Finset (Fin N))
    (hResidual:∀u,Rvertex u=Finset.univ\
      (outsideBufferedPathImage (n u) (inner u) (fC u) ∪ Finset.univ.image (finish u)))
    (hcover:∀u,Finset.univ.biUnion (fun i=>(q u i).support.toFinset)=Rvertex u ∪ Finset.univ.image (finish u))
    (hRimAvoid:∀u x y (hx:x∉bufferedPathStrictInterior (n u) (inner u))
      (hy:y∉bufferedPathStrictInterior (n u) (inner u)),(G u).Adj x y→
      ({fC u ⟨x,hx⟩,fC u ⟨y,hy⟩}:Finset (Fin N))∉Rrim)
    (hCC:∀u v,u≠v→Disjoint
      (((G u).induce {x | x∉bufferedPathStrictInterior (n u) (inner u)}).edgeFinset.image (Sym2.map (fC u)))
      (((G v).induce {x | x∉bufferedPathStrictInterior (n v) (inner v)}).edgeFinset.image (Sym2.map (fC v)))):
    HasFactorDecomposition H G:=by
  have hfixed:=@fixed_buffered_paths_from_residual_walks (Fin N) (Fin N) (Fin (D/2))
    inferInstance inferInstance inferInstance I inferInstance inferInstance
    G hG (physicalEdgeGraph Rrim) n ext inner hinner hwalk hdis start finish q hpath hlen hwalkDis
  obtain ⟨fA,hmatch,hA,hAA⟩:=hfixed (by simpa only using hwalkEdge)
  have hend:∀u i (p:Fin (n u i+1)),(p=0∨p=Fin.last (n u i))→
      ∀hp:inner u i p∉bufferedPathStrictInterior (n u) (inner u),
      fA u ⟨inner u i p,buffered_path_vertex_mem_domain (n u) (inner u) i p⟩=fC u ⟨inner u i p,hp⟩:=by
    intro u i p hp hpD
    rcases hp with rfl|rfl
    · rw [hmatch,(simple_walk_length_embedding_endpoints _ _ _ _ _).1,hstart]
    · rw [hmatch,(simple_walk_length_embedding_endpoints _ _ _ _ _).2,hfinish]
  apply marked_residual_identity_gives_factor_decomposition hEven H hH G hG I Rrim hRimHost n ext inner hinner hwalk fA fC
    (fun u x y hx hy hxy=>hA u ⟨x,hx⟩ ⟨y,hy⟩ hxy)
    (fun u x y hx hy hxy=>hC u ⟨x,hx⟩ ⟨y,hy⟩ hxy)
    hend start finish q hpath hlen hmatch hwalkDis Rvertex hResidual hcover hAA hRimAvoid
  intro u v huv
  exact partial_factor_sets_disjoint_of_edge_finsets _ _ (fC u) (fC v) (hCC u v huv)
end Oberwolfach
