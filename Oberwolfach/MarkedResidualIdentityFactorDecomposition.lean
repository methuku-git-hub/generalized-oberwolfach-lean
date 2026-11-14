module

public import Oberwolfach.MarkedResidualWalksFactorDecomposition
public import Oberwolfach.BufferedComplementImage

@[expose] public section
/-! Use the manuscript's residual-spoke identity to discharge the reserved
vertex disjointness and complement-image membership conditions. -/
set_option autoImplicit false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_residual_identity_gives_factor_decomposition
    {N D:ℕ} (hEven:Even D) (H:SimpleGraph (Fin N)) (hH:H.IsRegularOfDegree D)
    (G:Fin (D/2)→SimpleGraph (Fin N)) (hG:∀u,(G u).IsRegularOfDegree 2)
    (I:Fin (D/2)→Type*) [∀u,Fintype (I u)]
    (Rrim:Finset (Finset (Fin N))) (hRimHost:physicalEdgeGraph Rrim≤H)
    (n:∀u,I u→ℕ)
    (ext:∀u (i:I u),Fin (n u i+5)↪(Fin N)) (inner:∀u (i:I u),Fin (n u i+1)↪(Fin N))
    (hinner:∀u i p,inner u i p=ext u i ⟨p.val+2,by omega⟩)
    (hwalk:∀u i,∃p:(G u).Walk (ext u i ⟨0,by omega⟩) (ext u i ⟨n u i+4,by omega⟩),
      p.length=n u i+4 ∧ p.support=List.ofFn (ext u i))
    (fA:∀u,{x // x∈bufferedPathFullDomain (n u) (inner u)}↪(Fin N))
    (fC:∀u,{x // x∉bufferedPathStrictInterior (n u) (inner u)}↪(Fin N))
    (hAphys:∀u x y (hx:x∈bufferedPathFullDomain (n u) (inner u)) (hy:y∈bufferedPathFullDomain (n u) (inner u)),
      (G u).Adj x y→(physicalEdgeGraph Rrim).Adj (fA u ⟨x,hx⟩) (fA u ⟨y,hy⟩))
    (hC:∀u x y (hx:x∉bufferedPathStrictInterior (n u) (inner u)) (hy:y∉bufferedPathStrictInterior (n u) (inner u)),
      (G u).Adj x y→H.Adj (fC u ⟨x,hx⟩) (fC u ⟨y,hy⟩))
    (hend:∀u i (p:Fin (n u i+1)),(p=0 ∨ p=Fin.last (n u i))→
      ∀ hpD:inner u i p∉bufferedPathStrictInterior (n u) (inner u),
      fA u ⟨inner u i p,buffered_path_vertex_mem_domain (n u) (inner u) i p⟩=fC u ⟨inner u i p,hpD⟩)
    (start finish:∀u,I u→Fin N)
    (q:∀u (i:I u),(physicalEdgeGraph Rrim).Walk (start u i) (finish u i))
    (hpath:∀u i,(q u i).IsPath) (hlen:∀u i,(q u i).length=n u i)
    (hmatch:∀u i p,fA u ⟨inner u i p,buffered_path_vertex_mem_domain (n u) (inner u) i p⟩=
      simpleWalkLengthEmbedding (physicalEdgeGraph Rrim) (q u i) (hpath u i) (n u i) (hlen u i) p)
    (hwalkDis:∀u i j,i≠j→Disjoint (q u i).support.toFinset (q u j).support.toFinset)
    (Rvertex:Fin (D/2)→Finset (Fin N))
    (hResidual:∀u,Rvertex u=Finset.univ\
      (outsideBufferedPathImage (n u) (inner u) (fC u) ∪ Finset.univ.image (finish u)))
    (hcover:∀u,Finset.univ.biUnion (fun i=>(q u i).support.toFinset)=Rvertex u ∪ Finset.univ.image (finish u))
    (hAA:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x // x∈bufferedPathFullDomain (n u) (inner u)}
        ((G u).induce (↑(bufferedPathFullDomain (n u) (inner u)):Set (Fin N))) (fA u))
      (partialFactorPhysicalEdgesPoly {x // x∈bufferedPathFullDomain (n v) (inner v)}
        ((G v).induce (↑(bufferedPathFullDomain (n v) (inner v)):Set (Fin N))) (fA v)))
    (hRimAvoid:∀u x y (hx:x∉bufferedPathStrictInterior (n u) (inner u))
      (hy:y∉bufferedPathStrictInterior (n u) (inner u)),(G u).Adj x y→
      ({fC u ⟨x,hx⟩,fC u ⟨y,hy⟩}:Finset (Fin N))∉Rrim)
    (hCC:∀u v,u≠v→Disjoint
      (partialFactorPhysicalEdgesPoly {x // x∉bufferedPathStrictInterior (n u) (inner u)}
        ((G u).induce {x | x∉bufferedPathStrictInterior (n u) (inner u)}) (fC u))
      (partialFactorPhysicalEdgesPoly {x // x∉bufferedPathStrictInterior (n v) (inner v)}
        ((G v).induce {x | x∉bufferedPathStrictInterior (n v) (inner v)}) (fC v))) : HasFactorDecomposition H G := by
  let Z:Fin (D/2)→Finset (Fin N):=fun u=>outsideBufferedPathImage (n u) (inner u) (fC u)
  have hRZ:∀u,Disjoint (Rvertex u) (Z u):=by
    intro u
    exact residual_spoke_set_disjoint_complement (Rvertex u) (Z u) (Finset.univ.image (finish u)) (hResidual u)
  have hZ:∀u x (hx:x∉bufferedPathStrictInterior (n u) (inner u)),
      x∉bufferedPathFullDomain (n u) (inner u)→fC u ⟨x,hx⟩∈Z u:=by
    intro u x hx hxA
    exact outside_buffered_path_image_mem (n u) (inner u) (fC u) x hx hxA
  exact marked_residual_walks_give_factor_decomposition hEven H hH G hG I Rrim hRimHost n ext inner hinner hwalk
    fA fC hAphys hC hend start finish q hpath hlen hmatch hwalkDis Rvertex Z hRZ hcover hZ hAA hRimAvoid hCC
end Oberwolfach
