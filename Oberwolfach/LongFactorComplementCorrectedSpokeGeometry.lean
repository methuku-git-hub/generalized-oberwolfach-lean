module

public import Oberwolfach.LongCorrectedSpokeGeometry
public import Oberwolfach.LongFactorComplementProvenance

@[expose] public section
/-! Factor-complement provenance supplies the endpoint avoidance needed for
the corrected spoke geometry, on the same retained sample and residual. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance complementSpokeGeometryFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_factor_complement_corrected_spoke_geometry
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (S P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (hd:1≤d)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (Pack:Finset (Sym2 (Fin n))) (Enew:U→Finset (Sym2 (Fin n)))
    (A:Finset (Fin n×Fin n)) (R:U→Finset (Fin n))
    (hprov:LongFactorComplementProvenance F S P π d m raw t J Pack Enew A R):
    let Y:=fun u=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J u=>d) Subtype.val
    let H:Bool→Fin n→U→Prop:=fun b v u=>if b then retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t J false true true v u else v∈R u\Y u;
    (∀v u,¬(H false v u∧H true v u)) ∧
    (∀u v w,H false v u→H true w u→v≠π w):=by
  intro Y H
  have hEnd:∀u (i:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J u),(π^d) i.val∉R u:=by
    rcases hprov with ⟨ext,inner,fC,iso,hinner,hdis,hwalk,hσ,old,hPack,hOldDis,hA,hArcs,hImg,hR,hrest⟩
    intro u i
    rw [hR u]
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and,not_not,Finset.mem_union]
    right
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  exact long_corrected_spoke_geometry π d hd (fun e=>raw (Sum.inr e)) false true t J R hEnd
end Oberwolfach
