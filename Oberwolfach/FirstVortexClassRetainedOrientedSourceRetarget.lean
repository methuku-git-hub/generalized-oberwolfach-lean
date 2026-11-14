module

public import Oberwolfach.LongSelectedRetainedOrientedRetargetBadGraph
public import Oberwolfach.ClassInsertionBudget

@[expose] public section
/-! The regular-class required graph can replace the sampled required graph
in the same aligned source, spending its bounded insertion error. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstClassRetainedOrientedRetargetFin (n:ℕ):DecidableEq (Fin n):=selectedRetainedOrientedSourceWithLoadFin n

theorem first_vortex_class_retained_oriented_source_retarget
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hU:0<Fintype.card U) (F:U→SimpleGraph (Fin n)) (P S₀ S Used Sel:SimpleGraph (Fin n))
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ) (D:Fin n→Fin n→Prop)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (H:Finset U) (A:Finset (Fin n)) (absorber:U→Finset (Fin n))
    (δold δnew ξ:ℝ) (hSP:S≤P)
    (hedit:∀v,((changed (S₀.neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)
    (hmargin:ξ*n≤(δnew-δold)*(A.card:ℝ)):
    let Kold:=longRequiredPhysicalGraph P (S₀\Used) Sel π d A D (fun x y=>Used.Adj x y)
    let Knew:=longRequiredPhysicalGraph S (S\Used) Sel π d A D (fun x y=>Used.Adj x y)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:{z // z∈T}↪_:=Function.Embedding.subtype _;
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
      LongSelectedRetainedOrientedSourceWithLoad hU F P π d m ℓ raw t Jret σ H A Kold absorber δold M→
      LongSelectedRetainedOrientedSourceWithLoad hU F P π d m ℓ raw t Jret σ H A Knew absorber δnew M:=by
  intro Kold Knew T e M hsource
  have hchange:∀v∈A,(Knew.degree v:ℝ)≤(Kold.degree v:ℝ)+ξ*n:=by
    intro v hv
    have hbound:=(class_required_graph_edit_bounds P S₀ S Used Sel π d A D hSP).1 v
    have hins:=class_insertion_degree_le_edits S₀ S A v
    have hr:(Knew.degree v:ℝ)≤(Kold.degree v:ℝ)+(spanningRestriction (S\S₀) A).degree v:=by
      exact_mod_cast hbound
    have hi:((spanningRestriction (S\S₀) A).degree v:ℝ)≤
        (changed (S₀.neighborFinset v) (S.neighborFinset v)).card:=by
      exact_mod_cast hins
    linarith [hedit v]
  have hh:=long_selected_retained_oriented_source_retarget_bad_graph hU F P π d m ℓ raw t Jret σ H A Kold Knew absorber δold δnew (ξ*n) hchange hmargin
  have hdec:selectedRetainedOrientedRetargetFin n=firstClassRetainedOrientedRetargetFin n:=Subsingleton.elim _ _
  have hdecK:selectedRetainedOrientedRetargetFin K=firstClassRetainedOrientedRetargetFin K:=Subsingleton.elim _ _
  try rw [hdec] at hh
  try rw [hdecK] at hh
  exact hh M hsource
end Oberwolfach
