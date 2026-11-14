module

public import Oberwolfach.LongFactorResidualSpokePartition
public import Oberwolfach.MarkedIntervalSuccessorSeparation

@[expose] public section
/-! The exact factor complement supplies the two spoke geometry fields of
the corrected vortex records, including successor separation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance factorCorrectedSpokeGeometryFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

theorem long_factor_corrected_spoke_geometry
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (S P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (hd:2≤d) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (Pack:Finset (Sym2 (Fin n))) (Enew:U→Finset (Sym2 (Fin n)))
    (A:Finset (Fin n×Fin n)) (R:U→Finset (Fin n))
    (hprov:LongFactorComplementProvenance F S P π d m raw t J Pack Enew A R):
    let Y:=fun w=>markedIntervalRootSet π
      (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J w=>d) Subtype.val
    let HK:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t J false true true
    let H:=fun b v w=>if b then HK v w else v∈R w\Y w;
    (∀v u,¬(H false v u∧H true v u)) ∧
    (∀u v w,H false v u→H true w u→v≠π w):=by
  intro Y HK H
  have hpart:=long_factor_residual_spoke_partition F S P π d m hd hnoshort raw t J Pack Enew A R hprov
  have hcopy:=hprov
  unfold LongFactorComplementProvenance at hcopy
  rcases hcopy with ⟨ext,inner,fC,iso,hinner,hdis,hwalk,hσ,old,hExact,hOldDisj,hA,hsplit,hCompSplit,hR,hY,hstart,hfinish,hClass,hHost,hPacked⟩
  constructor
  · intro v u hv
    exact hpart.2.2 u v hv.2 hv.1
  · intro u v w hv hw heq
    have hwY:w∈Y u:=(hpart.1 u w).mp hw
    have havoid:=marked_residual_ordinary_avoids_successors π
      (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J u=>d) Subtype.val
      (outsideBufferedPathImage (fun _=>(m+1)*d) (inner u) (fC u)) (R u) (hR u)
    apply (Finset.disjoint_left.mp havoid) hv
    exact Finset.mem_image.mpr ⟨w,hwY,heq.symm⟩
end Oberwolfach
