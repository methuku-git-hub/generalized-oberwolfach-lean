module

public import Oberwolfach.ClassRequiredBudgetFromEdits
public import Oberwolfach.FirstVortexClassAssignmentWithoutMarkedBudget
public import Oberwolfach.LongRequiredAvoidsUsedPacking
public import Oberwolfach.InnerReservedGraph

@[expose] public section
/-! Transfer sampled graph budgets to the regular class without assuming a
bound on retained marked labels at a vertex. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance classNoMarkedEditsFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_class_assignment_from_edits_no_marked_budget
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P S₀ S Del Used Sel:SimpleGraph (Fin n)) (I:Finset (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (D:Fin n→Fin n→Prop)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t)
    (H:Finset U) (α b ρ₀ θ ε lam₀ lam ξ:ℝ) (Old:U→Finset (Fin n)) (Pack:Finset (Sym2 (Fin n)))
    (hn:0<n) (hU:0<Fintype.card U) (hρ₀:0<ρ₀) (hb:0≤b)
    (hbsmall:b≤((ρ₀/4)/40000)/16) (hαb:α/16≤b)
    (hSP:S≤P) (hedit:∀v,((changed (S₀.neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)
    (hξdeg:ξ≤α/32) (hξedges:ξ/2≤(lam-lam₀)*ε) (hPack:Pack⊆Used.edgeFinset)
    (hdegree:∀v,((longRequiredPhysicalGraph P (S₀\Used) Sel π d I D
      (fun x y=>Used.Adj x y)).degree v:ℝ)≤(α/32)*n)
    (hedges:((longRequiredPhysicalGraph P (S₀\Used) Sel π d I D
      (fun x y=>Used.Adj x y)).edgeFinset.card:ℝ)≤(θ*ε^2+lam₀*ε)*(n:ℝ)^2+24*d*n)
    (hJ:∀v,((spanningRestriction (P\Used) I\
      longRequiredPhysicalGraph P (S₀\Used) Sel π d I D (fun x y=>Used.Adj x y)).degree v:ℝ)≤ε*n):
    let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I D (fun x y=>Used.Adj x y)
    let Lbad:=protectedPairEdgeHubs (rawReservedSpokeList π d (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e)))) H
    let Bad:=fun v:Fin n=>Finset.univ.filter (fun w=>v∈retainedFinalMarkedAt π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) t Jret w)
    (∀w,Disjoint (rawReservedSpokeList π d (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) w) (Old w))→
    (∀e∈K.edgeFinset,((ρ₀/4)/40000)*n≤((Lbad e).card:ℝ))→
    FirstVortexClassPrescribedAssignmentNoMarkedBudget P S Del Used K I π d σE t Jret H α b ρ₀ θ ε lam Old Pack:=by
  intro K Lbad Bad hOld hLabels
  obtain ⟨hKd,hKe,hJd⟩:=class_required_budgets_from_edits P S₀ S Used Sel π d I D α θ ε lam₀ lam ξ
    hSP hedit hξdeg hξedges hdegree hedges hJ
  have hKPack:=long_required_graph_avoids_used_packing S (S\Used) Sel Used π d I D Pack (by intro x y h;exact h) hPack
  obtain ⟨_,hKJ,hUsedJ⟩:=inner_available_reserved_graph_bounds S Used K I
  exact first_vortex_class_assignment_without_marked_budget P S Del Used K I π d σE t Jret H α b ρ₀ θ ε lam Old Pack
    hn hU hρ₀ hb hbsmall hαb hKd hKe hKPack hJd hKJ hUsedJ hOld hLabels
end Oberwolfach
