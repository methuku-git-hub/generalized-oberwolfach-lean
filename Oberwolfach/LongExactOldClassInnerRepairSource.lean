module

public import Oberwolfach.LongExactOldDynamicBadRetarget
public import Oberwolfach.LongClassInnerRequiredRepair

@[expose] public section
/-! The dynamic source can be retargeted specifically to the unembedded-used
inner repair, charged to a bound on that actual deficit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance exactOldClassInnerRepairSourceFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_exact_old_class_inner_repair_source
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hU:0<Fintype.card U) (F:U→SimpleGraph (Fin n)) (P:SimpleGraph (Fin n))
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (H:Finset U) (A:Finset (Fin n)) (Kold S Used:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n))
    (δold δnew η:ℝ) (ExtraOld ExtraNew:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop)
    (hdeficit:∀Old Pack,ExtraOld Old Pack→∀v∈A,
      ((spanningRestriction ((S⊓Used)\SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))) A).degree v:ℝ)≤η)
    (hmargin:η≤(δnew-δold)*(A.card:ℝ))
    (hextra:∀Old Pack,Pack⊆Used.edgeFinset→ExtraOld Old Pack→ExtraNew Old Pack):
    let Knew:=fun Pack:Finset (Sym2 (Fin n))=>longClassInnerRequiredRepair S Used Kold A Pack
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:{z // z∈T}↪_:=Function.Embedding.subtype _;
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
    LongSelectedOrientedSourceExactOld hU F P π d m ℓ raw t Jret σ H A Kold Used absorber δold ExtraOld M→
    LongSelectedOrientedSourceDynamicBad hU F P π d m ℓ raw t Jret σ H A Knew Used absorber δnew ExtraNew M:=by
  intro Knew T e M hsource
  apply long_exact_old_dynamic_bad_retarget hU F P π d m ℓ raw t Jret σ H A Kold Used Knew absorber δold δnew η ExtraOld ExtraNew ?_ hmargin hextra M hsource
  intro Old Pack h v hv
  have hd:=graph_degree_sup_le Kold (spanningRestriction ((S⊓Used)\SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))) A) v
  have hd':((Knew Pack).degree v:ℝ)≤(Kold.degree v:ℝ)+
      (spanningRestriction ((S⊓Used)\SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))) A).degree v:=by
    have hdNat:(Knew Pack).degree v≤Kold.degree v+
        (spanningRestriction ((S⊓Used)\SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))) A).degree v:=by
      convert hd using 1 <;> congr! 5 <;> exact Subsingleton.elim _ _
    exact_mod_cast hdNat
  have hdef:((spanningRestriction ((S⊓Used)\SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))) A).degree v:ℝ)≤η:=by
    convert hdeficit Old Pack h v hv using 1 <;> congr! 4 <;> exact Subsingleton.elim _ _
  have hsum:((Knew Pack).degree v:ℝ)≤(Kold.degree v:ℝ)+η:=by
    linarith [hd',hdef]
  convert hsum using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
end Oberwolfach
