module

public import Oberwolfach.MarkedDecompositionSuppliesBufferedWalks
public import Oberwolfach.FixedBufferedWalksFactorDecomposition

@[expose] public section
/-! A marked-wheel decomposition glues to the already selected source-factor
complements, provided their endpoint and physical-edge identities hold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_decomposition_gives_fixed_factors
    {N D:ℕ} (hEven:Even D) (H:SimpleGraph (Fin N)) (hH:H.IsRegularOfDegree D)
    (F:Fin (D/2)→SimpleGraph (Fin N)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (E K:Type) [Fintype E] [Fintype K] (tail head:E→Fin N) (ktail khead:K→Fin N)
    (m b d:ℕ) (π:Equiv.Perm (Fin N)) (hb:1≤b) (H₀ Hₖ:Fin N→Fin (D/2)→Prop)
    (hdec:HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=Hₖ))
      (markedDecompositionTarget (markedPhysicalRimSet tail head ktail khead π) H₀ Hₖ))
    (I:Fin (D/2)→Type) [∀u,Fintype (I u)] [∀u,DecidableEq (I u)] (a:∀u,I u→Fin N)
    (hinj:∀u j,Function.Injective (fun i:Fin (d+1)=>(π^i.val) (a u j)))
    (hwindow:∀u (j l:I u),j≠l→Disjoint (permutationWindow π 0 d (a u j)) (permutationWindow π 0 d (a u l)))
    (hend:∀u j,(π^d) (a u j)∉Finset.univ.filter (fun x=>H₀ x u∨Hₖ x u))
    (hmarked:∀u x,Hₖ x u↔x∈markedIntervalRootSet π (fun _:I u=>d) (a u))
    (hsep:∀u x,Hₖ x u→¬H₀ x u)
    (hloopE:∀e:E,tail e≠head e) (hloopK:∀e:K,ktail e≠π (khead e))
    (hphysical:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hRimHost:physicalEdgeGraph (markedPhysicalRimSet tail head ktail khead π)≤H)
    (ext:∀u (i:I u),Fin ((m+1)*d+5)↪Fin N) (inner:∀u (i:I u),Fin ((m+1)*d+1)↪Fin N)
    (hinner:∀u i p,inner u i p=ext u i ⟨p.val+2,by omega⟩)
    (hwalk:∀u i,∃p:(F u).Walk (ext u i 0) (ext u i (Fin.last ((m+1)*d+4))),
      p.length=(m+1)*d+4 ∧ p.support=List.ofFn (ext u i))
    (hdis:∀u i j,i≠j→Disjoint (Finset.univ.image (ext u i)) (Finset.univ.image (ext u j)))
    (fC:∀u,{x // x∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner u)}↪Fin N)
    (hC:∀u x y,(F u).Adj x.1 y.1→H.Adj (fC u x) (fC u y))
    (hstart:∀u i (hp:inner u i 0∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner u)),fC u ⟨inner u i 0,hp⟩=a u i)
    (hfinish:∀u i (hp:inner u i (Fin.last ((m+1)*d))∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner u)),
      fC u ⟨inner u i (Fin.last ((m+1)*d)),hp⟩=(π^d) (a u i))
    (hResidual:∀u,(Finset.univ.filter (fun x=>H₀ x u∨Hₖ x u))=Finset.univ\
      (outsideBufferedPathImage (fun _=>(m+1)*d) (inner u) (fC u) ∪ Finset.univ.image (fun i:I u=>(π^d) (a u i))))
    (hRimAvoid:∀u x y (hx:x∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner u))
      (hy:y∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner u)),(F u).Adj x y→
      ({fC u ⟨x,hx⟩,fC u ⟨y,hy⟩}:Finset (Fin N))∉markedPhysicalRimSet tail head ktail khead π)
    (hCC:∀u v,u≠v→Disjoint
      (((F u).induce {x | x∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner u)}).edgeFinset.image (Sym2.map (fC u)))
      (((F v).induce {x | x∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner v)}).edgeFinset.image (Sym2.map (fC v)))):
    HasFactorDecomposition H F:=by
  obtain ⟨start,finish,hs,hf,q,hpath,hlen,hwalkDis,hcover,hcross⟩:=
    marked_decomposition_supplies_buffered_walks tail head ktail khead m b d π hb H₀ Hₖ hdec I a hinj hwindow hend hmarked hsep hloopE hloopK hphysical
  have hstart':∀u i (hp:inner u i 0∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner u)),fC u ⟨inner u i 0,hp⟩=start u i:=by
    intro u i hp
    exact (hstart u i hp).trans (hs u i).symm
  have hfinish':∀u i (hp:inner u i (Fin.last ((m+1)*d))∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner u)),
      fC u ⟨inner u i (Fin.last ((m+1)*d)),hp⟩=finish u i:=by
    intro u i hp
    exact (hfinish u i hp).trans (hf u i).symm
  have hResidual':∀u,(Finset.univ.filter (fun x=>H₀ x u∨Hₖ x u))=Finset.univ\
      (outsideBufferedPathImage (fun _=>(m+1)*d) (inner u) (fC u) ∪ Finset.univ.image (finish u)):=by
    intro u
    simpa only [funext (hf u)] using hResidual u
  exact fixed_buffered_walks_give_factor_decomposition hEven H hH F hF I _ hRimHost (fun _ _=>(m+1)*d)
    ext inner hinner hwalk hdis fC hC start finish hstart' hfinish' q hpath hlen hwalkDis hcross
    (fun u=>Finset.univ.filter (fun x=>H₀ x u∨Hₖ x u)) hResidual' hcover hRimAvoid hCC
end Oberwolfach
