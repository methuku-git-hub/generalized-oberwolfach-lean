module

public import Oberwolfach.LongFactorComplementProvenance
public import Oberwolfach.RetainedSpokesFromComplement

@[expose] public section
/-! The retained marked interval roots lie in the same witness's residual
spoke set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance factorRootsFin (n:ℕ):DecidableEq (Fin n):=factorComplementProvenanceFin n

theorem long_factor_provenance_roots_subset
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (Sclass P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (hd:2≤d) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (Pack:Finset (Sym2 (Fin n))) (Enew:U→Finset (Sym2 (Fin n)))
    (A:Finset (Fin n×Fin n)) (R:U→Finset (Fin n))
    (hprov:LongFactorComplementProvenance F Sclass P π d m raw t Jret Pack Enew A R):
    ∀w,markedIntervalRootSet π
      (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>d) Subtype.val⊆R w:=by
  unfold LongFactorComplementProvenance at hprov
  rcases hprov with ⟨ext,inner,fC,iso,hinner,hdis,hwalk,hσ,old,hExact,hOldDisj,hA,hsplit,hCompSplit,hR,hY,hstart,hfinish,hClass,hHost,hPacked⟩
  intro w
  have hg:=retained_marked_interval_geometry π d (by omega) hnoshort (fun e=>raw (Sum.inr e)) false t Jret
  exact marked_interval_roots_in_residual π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>d)
    Subtype.val (hg.1 w) (hg.2.1 w)
    (outsideBufferedPathImage (fun _=>(m+1)*d) (inner w) (fC w)) (R w) (hY w).symm (hR w)
end Oberwolfach
