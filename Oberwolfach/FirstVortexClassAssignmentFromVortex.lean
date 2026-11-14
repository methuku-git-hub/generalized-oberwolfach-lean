module

public import Oberwolfach.FirstVortexClassAssignmentFromEvent
public import Oberwolfach.MarkedInitialInnerVertexBound

@[expose] public section
/-! The first vortex vertex-size bound supplies the sampled residual-degree
condition for the class-specific assignment. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexClassVortexBoundFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_class_assignment_from_event_vortex_bound
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P S₀ S Del Used Sel:SimpleGraph (Fin n)) (Dv mv:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mv) (π:Equiv.Perm (Fin n)) (d:ℕ) (D:Fin n→Fin n→Prop)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t)
    (α b ρ₀ θ lam₀ lam ξ mAbs:ℝ) (Old:U→Finset (Fin n)) (Pack:Finset (Sym2 (Fin n)))
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
    (hmAbs:0<mAbs) (hUhi:Fintype.card U≤n) (hM:4/mAbs≤b/2)
    (hN:4*(n:ℝ)^(3/4:ℝ)≤b*n/2)
    (hOcc:∀v,((rawIntervalExtendedAnyHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) v).card:ℝ)≤
        4*(Fintype.card U:ℝ)/mAbs+4*(n:ℝ)^(3/4:ℝ)):
    FirstVortexClassPrescribedAssignmentOutcome P S Del Used
      (longRequiredPhysicalGraph S (S\Used) Sel π d (Q.extendedVertices 1) D (fun x y=>Used.Adj x y))
      (Q.extendedVertices 1) π d σE t Jret (Q.extendedIndices 1) α b ρ₀ θ ε lam Old Pack :=by
  have hI:((Q.extendedVertices 1).card:ℝ)≤ε*n:=by
    simpa only [Fintype.card_fin] using marked_initial_inner_vertex_bound Q hε
  let K₀:=longRequiredPhysicalGraph P (S₀\Used) Sel π d (Q.extendedVertices 1) D (fun x y=>Used.Adj x y)
  have hJ:∀v,((spanningRestriction (P\Used) (Q.extendedVertices 1)\K₀).degree v:ℝ)≤ε*n:=
    (inner_available_reserved_graph_at_host_scale P Used K₀ (Q.extendedVertices 1) ε hI).1
  exact first_vortex_class_assignment_from_event P S₀ S Del Used Sel Dv mv β ε Q π d D σE t Jret
    α b ρ₀ θ lam₀ lam ξ mAbs Old Pack hn hU hρ₀ hb hbsmall hαb hSP hedit hξdeg hξedges hPack
    hdegree hedges hJ hε hOld hUlo hεsmall herror hpair hmAbs hUhi hM hN hOcc
end Oberwolfach
