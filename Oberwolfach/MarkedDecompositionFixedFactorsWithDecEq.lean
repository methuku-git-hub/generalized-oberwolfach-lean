module

public import Oberwolfach.MarkedDecompositionFixedFactors

@[expose] public section
/-! Make the finite-vertex decidable-equality instance explicit in the
factor-reconstruction theorem. This transports only instance choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_decomposition_gives_fixed_factors_with_decEq
    {N D:ℕ} (decN:DecidableEq (Fin N)) (decU:DecidableEq (Fin (D/2))):
    letI:DecidableEq (Fin N):=decN
    letI:DecidableEq (Fin (D/2)):=decU;
    ∀ (hEven:Even D) (H:SimpleGraph (Fin N)) (hH:H.IsRegularOfDegree D)
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
      (((F v).induce {x | x∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner v)}).edgeFinset.image (Sym2.map (fC v)))),
    HasFactorDecomposition H F:=by
  have heq:decN=instDecidableEqFin N:=Subsingleton.elim _ _
  have heqU:decU=instDecidableEqFin (D/2):=Subsingleton.elim _ _
  cases heq
  cases heqU
  exact @marked_decomposition_gives_fixed_factors N D
end Oberwolfach
