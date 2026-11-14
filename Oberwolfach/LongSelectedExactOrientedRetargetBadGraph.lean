module

public import Oberwolfach.LongSelectedExactOrientedSourceWithLoad

@[expose] public section
/-! Retarget an aligned source to a new required-edge graph, charging its
additional local degree to an explicitly available load margin. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance selectedExactOrientedRetargetFin (n:ℕ):DecidableEq (Fin n):=selectedExactOrientedSourceWithLoadFin n

theorem long_selected_exact_oriented_source_retarget_bad_graph
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hU:0<Fintype.card U) (F:U→SimpleGraph (Fin n)) (P:SimpleGraph (Fin n))
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (H:Finset U) (A:Finset (Fin n)) (Kold Knew:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n))
    (δold δnew η:ℝ)
    (hchange:∀v∈A,(Knew.degree v:ℝ)≤(Kold.degree v:ℝ)+η)
    (hmargin:η≤(δnew-δold)*(A.card:ℝ)):
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:{z // z∈T}↪_:=Function.Embedding.subtype _;
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
      LongSelectedExactOrientedSourceWithLoad hU F P π d m ℓ raw t Jret σ H A Kold absorber δold M→
      LongSelectedExactOrientedSourceWithLoad hU F P π d m ℓ raw t Jret σ H A Knew absorber δnew M:=by
  intro T e M hsource
  unfold LongSelectedExactOrientedSourceWithLoad at hsource ⊢
  have hdec:selectedExactOrientedSourceWithLoadFin n=selectedExactOrientedRetargetFin n:=Subsingleton.elim _ _
  have hdecK:selectedExactOrientedSourceWithLoadFin K=selectedExactOrientedRetargetFin K:=Subsingleton.elim _ _
  try rw [hdec] at hsource ⊢
  try rw [hdecK] at hsource ⊢
  rcases hsource with ⟨Dsrc,orig,hpair,hcycles,hwhole,hArcs,E,halign,hres,ext,paths,ψ,assign,data,hprops,hload,pieces,hgraph,harcs,Pack,hdis,hsub,hLayer,hAvoid,hExact,hEq,hhub,hsize⟩
  refine ⟨Dsrc,orig,hpair,hcycles,hwhole,hArcs,E,halign,hres,ext,paths,ψ,assign,data,hprops,?_,pieces,hgraph,harcs,Pack,hdis,hsub,hLayer,hAvoid,hExact,hEq,hhub,hsize⟩
  intro occupied Z v hv
  have hh:=hload v hv
  have hc:=hchange v hv
  nlinarith
end Oberwolfach
