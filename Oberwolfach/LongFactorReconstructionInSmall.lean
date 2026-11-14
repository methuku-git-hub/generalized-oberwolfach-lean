module

public import Oberwolfach.LongFactorProvenanceReconstructionCore
public import Oberwolfach.LongComplementImageInSmall

@[expose] public section
/-! Project the retained same-sample complement witness to exactly the
source-path and physical-edge data needed by the reconstruction theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance factorCoreSmallFin (n:ℕ):DecidableEq (Fin n):=factorCoreFin n

theorem long_factor_provenance_reconstruction_in_small
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (Sclass P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (Pack:Finset (Sym2 (Fin n))) (Enew:U→Finset (Sym2 (Fin n)))
    (A:Finset (Fin n×Fin n)) (R:U→Finset (Fin n))
    (hprov:LongFactorComplementProvenance F Sclass P π d m raw t Jret Pack Enew A R)
    (Small:SimpleGraph (Fin n)) (hSmall:Small.edgeFinset=A.image (fun a=>s(a.1,a.2))):
    let I:=fun w=>retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w
    ∃(ext:∀w,I w→Fin ((m+1)*d+5)↪Fin n)
      (inner:∀w,I w→Fin ((m+1)*d+1)↪Fin n)
      (fC:∀w,{x // x∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)}↪Fin n),
      (∀w i p,inner w i p=ext w i ⟨p.val+2,by omega⟩) ∧
      (∀w i j,i≠j→Disjoint (Finset.univ.image (ext w i)) (Finset.univ.image (ext w j))) ∧
      (∀w i,∃p:(F w).Walk (ext w i 0) (ext w i (Fin.last ((m+1)*d+4))),p.length=(m+1)*d+4 ∧ p.support=List.ofFn (ext w i)) ∧
      (∀w,R w=Finset.univ\(outsideBufferedPathImage (fun _=>(m+1)*d) (inner w) (fC w) ∪ Finset.univ.image (fun j:I w=>(π^d) j.val))) ∧
      (∀w i (hp:inner w i 0∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)),fC w ⟨inner w i 0,hp⟩=i.val) ∧
      (∀w i (hp:inner w i (Fin.last ((m+1)*d))∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)),fC w ⟨inner w i (Fin.last ((m+1)*d)),hp⟩=(π^d) i.val) ∧
      (∀w x y,(F w).Adj x.1 y.1→Sclass.Adj (fC w x) (fC w y)) ∧
      (∀w z,w≠z→Disjoint
        (((F w).induce {x | x∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)}).edgeFinset.image (Sym2.map (fC w)))
        (((F z).induce {x | x∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner z)}).edgeFinset.image (Sym2.map (fC z)))) ∧
      ∀w,(((F w).induce {x | x∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)}).edgeFinset.image (Sym2.map (fC w)))⊆Small.edgeFinset:=by
  intro I
  obtain ⟨ext,inner,fC,hinner,hdis,hwalk,hR,hstart,hfinish,hClass,hPacked,arcs,hA,hcomp⟩:=
    long_factor_provenance_reconstruction_core F Sclass P π d m raw t Jret Pack Enew A R hprov
  refine ⟨ext,inner,fC,hinner,hdis,hwalk,hR,hstart,hfinish,hClass,hPacked,?_⟩
  exact long_complement_image_in_small
    (fun w=>(F w).induce {x | x∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)})
    (fun w=>fC w) arcs A Small hA hSmall hcomp
end Oberwolfach
