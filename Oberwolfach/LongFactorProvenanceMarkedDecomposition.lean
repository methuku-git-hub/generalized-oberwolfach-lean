module

public import Oberwolfach.LongFactorReconstructionInSmall
public import Oberwolfach.LongFactorResidualSpokePartition
public import Oberwolfach.RetainedMarkedIntervalGeometry
public import Oberwolfach.MarkedDecompositionFixedFactorsWithDecEq

@[expose] public section
/-! Reconstruct the prescribed factors from the actual complement provenance
and a marked decomposition of the same residual. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance provenanceMarkedFactorFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

theorem long_factor_provenance_marked_decomposition
    {n D:ℕ} (hEven:Even D) (S P:SimpleGraph (Fin n)) (hS:S.IsRegularOfDegree D)
    (F:Fin (D/2)→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (π:Equiv.Perm (Fin n)) (d m b:ℕ) (hd:2≤d) (hb:1≤b)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (raw:RawMarkedOutcome (Fin n) (Fin (D/2)) Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (Pack:Finset (Sym2 (Fin n))) (Enew:Fin (D/2)→Finset (Sym2 (Fin n)))
    (A:Finset (Fin n×Fin n)) (R:Fin (D/2)→Finset (Fin n))
    (hprov:LongFactorComplementProvenance F S P π d m raw t J Pack Enew A R)
    (Small:SimpleGraph (Fin n)) (hSmall:Small.edgeFinset=A.image (fun a=>s(a.1,a.2)))
    (E K:Type) [Fintype E] [Fintype K] (tail head:E→Fin n) (ktail khead:K→Fin n)
    (hloopE:∀e:E,tail e≠head e) (hloopK:∀e:K,ktail e≠π (khead e))
    (hphysical:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hRimHost:physicalEdgeGraph (markedPhysicalRimSet tail head ktail khead π)≤S)
    (hAvoid:∀x y,Small.Adj x y→({x,y}:Finset (Fin n))∉markedPhysicalRimSet tail head ktail khead π):
    let Y:=fun u=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J u=>d) Subtype.val
    let H₀:=fun v u=>v∈R u\Y u
    let HK:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t J false true true;
    HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK))
      (markedDecompositionTarget (markedPhysicalRimSet tail head ktail khead π) H₀ HK) →
    HasFactorDecomposition S F :=by
  intro Y H₀ HK hdec
  let I:=fun u=>retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J u
  letI : ∀u,DecidableEq (I u):=fun _=>Classical.decEq _
  have hpart:=long_factor_residual_spoke_partition F S P π d m hd hnoshort raw t J Pack Enew A R hprov
  have hgeom:=retained_marked_interval_geometry π d (by omega) hnoshort (fun e=>raw (Sum.inr e)) false t J
  obtain ⟨ext,inner,fC,hinner,hdis,hwalk,hR,hstart,hfinish,hClass,hCC,hCompSmall⟩:=
    long_factor_provenance_reconstruction_in_small F S P π d m raw t J Pack Enew A R hprov Small hSmall
  have hres:∀u,(Finset.univ.filter (fun x=>H₀ x u∨HK x u))=R u:=by
    intro u
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact (hpart.2.1 u x).symm
  have hend:∀u (i:I u),(π^d) i.val∉Finset.univ.filter (fun x=>H₀ x u∨HK x u):=by
    intro u i
    rw [hres,hR u]
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,not_not,Finset.mem_union]
    right
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hRimAvoid:∀u x y (hx:x∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner u))
      (hy:y∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner u)),(F u).Adj x y→
      ({fC u ⟨x,hx⟩,fC u ⟨y,hy⟩}:Finset (Fin n))∉markedPhysicalRimSet tail head ktail khead π:=by
    intro u x y hx hy hxy
    have hed:s(fC u ⟨x,hx⟩,fC u ⟨y,hy⟩)∈Small.edgeFinset:=hCompSmall u
      (Finset.mem_image.mpr ⟨s(⟨x,hx⟩,⟨y,hy⟩),SimpleGraph.mem_edgeFinset.mpr hxy,rfl⟩)
    exact hAvoid _ _ (SimpleGraph.mem_edgeFinset.mp hed)
  have hResidual:∀u,(Finset.univ.filter (fun x=>H₀ x u∨HK x u))=Finset.univ\
      (outsideBufferedPathImage (fun _=>(m+1)*d) (inner u) (fC u) ∪ Finset.univ.image (fun i:I u=>(π^d) i.val)):=by
    intro u
    rw [hres]
    exact hR u
  exact marked_decomposition_gives_fixed_factors_with_decEq (provenanceMarkedFactorFin n) (provenanceMarkedFactorFin (D/2)) hEven S hS F hF E K tail head ktail khead m b d π hb H₀ HK hdec I
    (fun _ i=>i.val) hgeom.1 hgeom.2.1 (by intro u i; convert hend u i using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) (by intro u x; convert hpart.1 u x using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hpart.2.2 hloopE hloopK hphysical hRimHost
    ext inner hinner hwalk hdis fC hClass hstart hfinish (by intro u; convert hResidual u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hRimAvoid hCC
end Oberwolfach
