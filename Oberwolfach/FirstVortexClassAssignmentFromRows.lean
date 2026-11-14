module

public import Oberwolfach.FirstVortexClassAssignmentFromVortex
public import Oberwolfach.LongRequiredVortexRowMargins

@[expose] public section
/-! The first-inner physical row and approximate-residual bound supply the
sampled graph budgets required by the actual class assignment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstClassRowsFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n
local instance (priority := 2000) firstClassRowsSix : DecidableEq (Fin 6) := instDecidableEqFin 6

theorem first_vortex_class_assignment_from_rows
    (α lam₀:ℝ) (d:ℕ) (hα:0<α) (hlam₀:0<lam₀) (hd:1≤d):
    ∃N:ℕ,∀n:ℕ,N≤n→∀ {U:Type} [Fintype U] [DecidableEq U]
    (P S₀ S Del Used Sel:SimpleGraph (Fin n)) (Dv mv:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mv) (π:Equiv.Perm (Fin n)) (D:Fin n→Fin n→Prop)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t)
    (b ρ₀ θ lam ξ mAbs C₀ u:ℝ) (Old:U→Finset (Fin n)) (Pack:Finset (Sym2 (Fin n)))
    (hn:0<n) (hU:0<Fintype.card U) (hρ₀:0<ρ₀) (hb:0≤b)
    (hbsmall:b≤((ρ₀/4)/40000)/16) (hαb:α/16≤b)
    (hSP:S≤P) (hedit:∀v,((changed (S₀.neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)
    (hξdeg:ξ≤α/32) (hξedges:ξ/2≤(lam-lam₀)*ε) (hPack:Pack⊆Used.edgeFinset)
    (hS₀:S₀=longPhysicalStateGraph P σE {0,1,2,3,4})
    (hSelected:∀x∈Q.extendedVertices 1,∀y∈Q.extendedVertices 1,
      (longSelectedPhysicalGraph P π d σE).Adj x y→Sel.Adj x y)
    (hθ:0≤θ) (hθhi:θ≤1/100) (hC:1≤C₀) (hehi:ε≤(α/2)/(1000*C₀))
    (hlamhi:lam₀≤(α/2)/128) (hu:0≤u) (huhi:u≤2*θ)
    (hrow:∀v∈Q.extendedVertices 1,
      |(((P.neighborFinset v∩Q.extendedVertices 1).filter (fun w=>(σE (Sum.inl s(v,w))).1=4)).card:ℝ)-
        u*(P.neighborFinset v∩Q.extendedVertices 1).card|<(n:ℝ)^(3/4:ℝ))
    (hB:∀v∈Q.extendedVertices 1,
      ((longPhysicalStateGraph P σE {2,3}\Used).degree v:ℝ)≤lam₀*n)
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
        4*(Fintype.card U:ℝ)/mAbs+4*(n:ℝ)^(3/4:ℝ)),
    FirstVortexClassPrescribedAssignmentOutcome P S Del Used
      (longRequiredPhysicalGraph S (S\Used) Sel π d (Q.extendedVertices 1) D (fun x y=>Used.Adj x y))
      (Q.extendedVertices 1) π d σE t Jret (Q.extendedIndices 1) α b ρ₀ θ ε lam Old Pack :=by
  have hαhalf:0<α/2:=by positivity
  obtain ⟨N,hN⟩:=long_required_vortex_row_margins (α/2) lam₀ hαhalf hlam₀ d hd
  refine ⟨N,?_⟩
  intro n hnN U _ _ P S₀ S Del Used Sel Dv mv β ε Q π D σE t Jret b ρ₀ θ lam ξ mAbs C₀ u Old Pack hn hU hρ₀ hb hbsmall hαb hSP hedit hξdeg hξedges hPack hS₀ hSelected hθ hθhi hC hehi hlamhi hu huhi hrow hB hε hOld hUlo hεsmall herror hpair hmAbs hUhi hM hNabs hOcc
  have hP₀:S₀\Used≤longPhysicalStateGraph P σE {0,1,2,3,4}\Used:=by rw [hS₀]
  have horder:N≤Fintype.card (Fin n):=by simpa using hnN
  obtain ⟨hdegree,hedges⟩:=hN (Fin n) U Bool Bool P (S₀\Used) Sel Used Dv mv β ε Q horder π D
    (fun x y=>Used.Adj x y) σE hP₀ hSelected θ C₀ u hθ hθhi hε hC hehi hlamhi hu huhi
    (by simpa only [Fintype.card_fin] using hrow) (by simpa only [Fintype.card_fin] using hB)
  have hdegree':∀v,((longRequiredPhysicalGraph P (S₀\Used) Sel π d (Q.extendedVertices 1) D
      (fun x y=>Used.Adj x y)).degree v:ℝ)≤(α/32)*n:=by
    intro v
    have hh:=hdegree v
    simp only [Fintype.card_fin] at hh
    linarith
  have hedges':((longRequiredPhysicalGraph P (S₀\Used) Sel π d (Q.extendedVertices 1) D
      (fun x y=>Used.Adj x y)).edgeFinset.card:ℝ)≤(θ*ε^2+lam₀*ε)*(n:ℝ)^2+24*d*n:=by
    simpa only [Fintype.card_fin] using hedges
  exact first_vortex_class_assignment_from_event_vortex_bound P S₀ S Del Used Sel Dv mv β ε Q π d D σE t Jret
    α b ρ₀ θ lam₀ lam ξ mAbs Old Pack hn hU hρ₀ hb hbsmall hαb hSP hedit hξdeg hξedges hPack
    hdegree' hedges' hε hOld hUlo hεsmall herror hpair hmAbs hUhi hM hNabs hOcc
end Oberwolfach
