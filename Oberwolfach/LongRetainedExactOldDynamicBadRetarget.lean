module

public import Oberwolfach.LongSelectedRetainedSourceExactOld
public import Oberwolfach.LongSelectedRetainedSourceDynamicBad
public import Oberwolfach.LongSelectedRetainedSourceExactOld
public import Oberwolfach.LongSelectedRetainedSourceDynamicBad

@[expose] public section
/-! Retarget after choosing the exact embedded old packing.  The new required
graph may depend on that packing, and its local cost is charged to the
available source load margin. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance retainedExactOldDynamicRetargetFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_retained_exact_old_dynamic_bad_retarget
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hU:0<Fintype.card U) (F:U→SimpleGraph (Fin n)) (P:SimpleGraph (Fin n))
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (H:Finset U) (A:Finset (Fin n)) (Kold Used:SimpleGraph (Fin n))
    (Knew:Finset (Sym2 (Fin n))→SimpleGraph (Fin n)) (absorber:U→Finset (Fin n))
    (δold δnew η:ℝ) (ExtraOld ExtraNew:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop)
    (hchange:∀Old Pack,ExtraOld Old Pack→∀v∈A,((Knew Pack).degree v:ℝ)≤(Kold.degree v:ℝ)+η)
    (hmargin:η≤(δnew-δold)*(A.card:ℝ))
    (hextra:∀Old Pack,Pack⊆Used.edgeFinset→ExtraOld Old Pack→ExtraNew Old Pack):
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:{z // z∈T}↪_:=Function.Embedding.subtype _;
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
    LongSelectedRetainedSourceExactOld hU F P π d m ℓ raw t Jret σ H A Kold Used absorber δold ExtraOld M→
    LongSelectedRetainedSourceDynamicBad hU F P π d m ℓ raw t Jret σ H A Knew Used absorber δnew ExtraNew M:=by
  intro T e M hsource
  unfold LongSelectedRetainedSourceExactOld at hsource
  unfold LongSelectedRetainedSourceDynamicBad
  have ha:selectedRetainedSourceExactOldFin n=retainedExactOldDynamicRetargetFin n:=Subsingleton.elim _ _
  have hb:selectedRetainedSourceDynamicBadFin n=retainedExactOldDynamicRetargetFin n:=Subsingleton.elim _ _
  have hc:selectedRetainedSourceExactOldFin K=retainedExactOldDynamicRetargetFin K:=Subsingleton.elim _ _
  have hd:selectedRetainedSourceDynamicBadFin K=retainedExactOldDynamicRetargetFin K:=Subsingleton.elim _ _
  try rw [ha,hc] at hsource
  try rw [hb,hd]
  rcases hsource with ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hload,pieces,hpieceEdge,hpieceArc,Pack,hExact,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra⟩
  refine ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,pieces,hpieceEdge,hpieceArc,Pack,hExact,?_,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hextra _ Pack hUsed hExtra⟩
  intro occupied Z v hv
  have hh:=hload v hv
  have hc:=hchange _ Pack hExtra v hv
  nlinarith
end Oberwolfach
