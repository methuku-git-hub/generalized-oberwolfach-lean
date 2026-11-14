module

public import Oberwolfach.LongSelectedClassDynamicSourceSameBalanced

@[expose] public section
/-! The original factor-complement maps, canonical arc images and the old/new
edge split are retained together for subsequent factor reconstruction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance factorComplementProvenanceFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

def LongFactorComplementProvenance
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (Sclass P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (Pack:Finset (Sym2 (Fin n))) (Enew:U→Finset (Sym2 (Fin n)))
    (A:Finset (Fin n×Fin n)) (R:U→Finset (Fin n)):Prop:=
  ∃(ext:∀w,retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w→Fin ((m+1)*d+5)↪Fin n)
    (inner:∀w,retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w→Fin ((m+1)*d+1)↪Fin n)
    (fC:∀w,{x // x∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)}↪Fin n)
    (iso:∀w (C:(F w).ConnectedComponent),SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (hinner:∀w i p,inner w i p=ext w i ⟨p.val+2,by omega⟩)
    (hdis:∀w i j,i≠j→Disjoint (Finset.univ.image (ext w i)) (Finset.univ.image (ext w j)))
    (hwalk:∀w i,∃p:(F w).Walk (ext w i 0) (ext w i (Fin.last ((m+1)*d+4))),
      p.length=(m+1)*d+4 ∧ p.support=List.ofFn (ext w i))
    (hσ:∀w,(complementTailDomain (bufferedPathFullDomain (fun _=>(m+1)*d) (inner w))
      (bufferedFinalEndpoints (fun _=>(m+1)*d) (inner w))).image (factorCycleOrientation (F w) (iso w))=
      complementTailDomain (bufferedPathFullDomain (fun _=>(m+1)*d) (inner w))
        (bufferedInitialEndpoints (fun _=>(m+1)*d) (inner w))),
  let tail:=fun w=>bufferedOrientedTailEmbedding (fun _=>(m+1)*d) (ext w) (inner w) (hinner w) (hdis w) (fC w)
  let head:=fun w=>bufferedOrientedHeadEmbedding (fun _=>(m+1)*d) (ext w) (inner w) (hinner w) (hdis w) (factorCycleOrientation (F w) (iso w)) (hσ w) (fC w)
  let arcs:=fun w=>Finset.univ.image (fun x=>(tail w x,head w x))
  ∃old:U→Finset (Sym2 (Fin n)),
    Pack=Finset.univ.biUnion old ∧
    (∀w z,w≠z→Disjoint (old w) (old z)) ∧
    A=Finset.univ.biUnion arcs ∧
    (∀w,(arcs w).image (fun a=>s(a.1,a.2))=old w∪Enew w) ∧
    (∀w,(((F w).induce {x | x∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)}).edgeFinset).image (Sym2.map (fC w))=old w∪Enew w) ∧
    (∀w,R w=Finset.univ\(outsideBufferedPathImage (fun _=>(m+1)*d) (inner w) (fC w) ∪
      Finset.univ.image (fun j:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>(π^d) j.val))) ∧
    (∀w,Disjoint (outsideBufferedPathImage (fun _=>(m+1)*d) (inner w) (fC w))
      (markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>d) Subtype.val)) ∧
    (∀w i (hp:inner w i 0∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)),fC w ⟨inner w i 0,hp⟩=i.val) ∧
    (∀w i (hp:inner w i (Fin.last ((m+1)*d))∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)),
      fC w ⟨inner w i (Fin.last ((m+1)*d)),hp⟩=(π^d) i.val) ∧
    (∀w x y,(F w).Adj x.1 y.1→Sclass.Adj (fC w x) (fC w y)) ∧
    (∀w x y,(F w).Adj x.1 y.1→P.Adj (fC w x) (fC w y)) ∧
    (∀w z,w≠z→Disjoint
      (((F w).induce {x | x∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)}).edgeFinset.image (Sym2.map (fC w)))
      (((F z).induce {x | x∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner z)}).edgeFinset.image (Sym2.map (fC z))))
end Oberwolfach
