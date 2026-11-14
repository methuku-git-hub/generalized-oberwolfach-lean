module

public import Oberwolfach.FirstVortexClassAssignmentFromEditsNoMarkedBudget
public import Oberwolfach.GenericRetainedMatchingLabels
public import Oberwolfach.MarkedInitialInnerVertexBound
public import Oberwolfach.MarkedInitialInnerHubBound

@[expose] public section
/-! Reserved-pair tests and the vortex size bounds provide the class-specific
assignment without any global retained-marked-degree hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance classEventNoMarkedFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_class_assignment_from_event_no_marked_budget
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P S₀ S Del Used Sel:SimpleGraph (Fin n)) (Dv mv:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mv) (π:Equiv.Perm (Fin n)) (d:ℕ) (D:Fin n→Fin n→Prop)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t)
    (α b ρ₀ θ lam₀ lam ξ:ℝ) (Old:U→Finset (Fin n)) (Pack:Finset (Sym2 (Fin n)))
    (hn:0<n) (hU:0<Fintype.card U) (hρ₀:0<ρ₀) (hb:0≤b)
    (hbsmall:b≤((ρ₀/4)/40000)/16) (hαb:α/16≤b)
    (hSP:S≤P) (hedit:∀v,((changed (S₀.neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)
    (hξdeg:ξ≤α/32) (hξedges:ξ/2≤(lam-lam₀)*ε) (hPack:Pack⊆Used.edgeFinset)
    (hdegree:∀v,((longRequiredPhysicalGraph P (S₀\Used) Sel π d (Q.extendedVertices 1) D
      (fun x y=>Used.Adj x y)).degree v:ℝ)≤(α/32)*n)
    (hedges:((longRequiredPhysicalGraph P (S₀\Used) Sel π d (Q.extendedVertices 1) D
      (fun x y=>Used.Adj x y)).edgeFinset.card:ℝ)≤(θ*ε^2+lam₀*ε)*(n:ℝ)^2+24*d*n)
    (hε:0≤ε) (hOld:∀w,Disjoint (rawReservedSpokeList π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) w) (Old w))
    (hUlo:(ρ₀/4)*n≤Fintype.card U) (hεsmall:ε≤(ρ₀/4)/80000)
    (herror:(n:ℝ)^(3/4:ℝ)≤(ρ₀/4)*n/80000)
    (hpair:∀x y,x≠y→(5/8:ℝ)*(1/100:ℝ)^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
      (((Finset.univ:Finset U).filter (fun w=>rawIntervalFamilyState π d
        (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) (x,w)=some (Sum.inr false) ∧
        rawIntervalFamilyState π d (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) (y,w)=some (Sum.inr false))).card:ℝ))
    (hUhi:Fintype.card U≤n):
    FirstVortexClassPrescribedAssignmentNoMarkedBudget P S Del Used
      (longRequiredPhysicalGraph S (S\Used) Sel π d (Q.extendedVertices 1) D (fun x y=>Used.Adj x y))
      (Q.extendedVertices 1) π d σE t Jret (Q.extendedIndices 1) α b ρ₀ θ ε lam Old Pack :=by
  let raw:=fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))
  let K:=longRequiredPhysicalGraph S (S\Used) Sel π d (Q.extendedVertices 1) D (fun x y=>Used.Adj x y)
  have hI:((Q.extendedVertices 1).card:ℝ)≤ε*n:=by
    simpa only [Fintype.card_fin] using marked_initial_inner_vertex_bound Q hε
  let K₀:=longRequiredPhysicalGraph P (S₀\Used) Sel π d (Q.extendedVertices 1) D (fun x y=>Used.Adj x y)
  have hJ:∀v,((spanningRestriction (P\Used) (Q.extendedVertices 1)\K₀).degree v:ℝ)≤ε*n:=
    (inner_available_reserved_graph_at_host_scale P Used K₀ (Q.extendedVertices 1) ε hI).1
  have hρ:0≤ρ₀/4:=by positivity
  have hinner:((Q.extendedIndices 1).card:ℝ)≤(ρ₀/4)*n/80000:=by
    have hh:=marked_initial_inner_hub_bound P Dv mv β ε Q hε (by simpa using hUhi)
    have hh':=mul_le_mul_of_nonneg_right hεsmall (Nat.cast_nonneg n)
    simp only [Fintype.card_fin] at hh
    nlinarith
  obtain ⟨_,_,hLabels⟩:=generic_reserved_pair_matching_hypotheses
    π d raw (Q.extendedIndices 1) Old hOld K (fun _=>∅) n (ρ₀/4) hρ hUlo hinner herror hpair
  exact first_vortex_class_assignment_from_edits_no_marked_budget P S₀ S Del Used Sel (Q.extendedVertices 1) π d D σE
    t Jret (Q.extendedIndices 1) α b ρ₀ θ ε lam₀ lam ξ Old Pack hn hU hρ₀ hb hbsmall hαb
    hSP hedit hξdeg hξedges hPack hdegree hedges hJ hOld hLabels
end Oberwolfach
