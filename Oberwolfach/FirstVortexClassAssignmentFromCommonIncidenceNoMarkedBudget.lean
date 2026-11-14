module

public import Oberwolfach.FirstVortexClassAssignmentFromRowsNoMarkedBudget
public import Oberwolfach.LongApproximateResidualMatchingMargins

@[expose] public section
/-! The matching incidence event and first-inner physical row supply the
actual regular-class bad-edge assignment on the same surviving matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstClassIncidenceFinNoMarked (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n
local instance (priority := 2000) firstClassIncidenceSixNoMarked : DecidableEq (Fin 6) := instDecidableEqFin 6

theorem first_vortex_class_assignment_from_common_incidence_no_marked_budget
    (α lam₀:ℝ) (d:ℕ) (hα:0<α) (hlam₀:0<lam₀) (hd:1≤d):
    ∃N:ℕ,∀n:ℕ,N≤n→∀ {U C:Type} [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]
    (P S₀ S Del Used Sel:SimpleGraph (Fin n)) (Dv mv:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mv) (π:Equiv.Perm (Fin n)) (D:Fin n→Fin n→Prop)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t)
    (b ρ₀ θ lam ξ C₀ u:ℝ) (Old:U→Finset (Fin n)) (Pack:Finset (Sym2 (Fin n)))
    (g j:Bool) (R:C→Finset (LongRawHubResource n U)) (rate γ δloss:ℝ),
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σE e)
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let Src:=longRawSurvivingResources P π d raw g j Del.edgeFinset
    let q:=survivingCandidateEmbedding R Src T (long_raw_surviving_resources_subset P π d raw g j Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j;
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈Src))))
    (hUsed:Used=physicalRimCandidateUnion φ (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (M.map q))
    (hγ:0≤γ) (hDel:∀x,(Del.degree x:ℝ)≤δloss)
    (hsmall:2*max rate (4*γ)≤lam₀/3) (hδloss:δloss≤(lam₀/3)*n)
    (hmatch:∀i,((longRawIncidenceSet Src i\M.biUnion (restrictedResourceSet R (Function.Embedding.subtype (·∈Src)))).card:ℝ)≤
      max (rate*n) (γ*(longRawIncidenceSet Src i).card))
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
    (hε:0≤ε) (hOld:∀w,Disjoint (rawReservedSpokeList π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) w) (Old w))
    (hUlo:(ρ₀/4)*n≤Fintype.card U) (hεsmall:ε≤(ρ₀/4)/80000)
    (herror:(n:ℝ)^(3/4:ℝ)≤(ρ₀/4)*n/80000)
    (hpair:∀x y,x≠y→(5/8:ℝ)*(1/100:ℝ)^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
      (((Finset.univ:Finset U).filter (fun w=>rawIntervalFamilyState π d
        (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) (x,w)=some (Sum.inr false) ∧
        rawIntervalFamilyState π d (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) (y,w)=some (Sum.inr false))).card:ℝ))
    (hUhi:Fintype.card U≤n),
    FirstVortexClassPrescribedAssignmentNoMarkedBudget P S Del Used
      (longRequiredPhysicalGraph S (S\Used) Sel π d (Q.extendedVertices 1) D (fun x y=>Used.Adj x y))
      (Q.extendedVertices 1) π d σE t Jret (Q.extendedIndices 1) α b ρ₀ θ ε lam Old Pack :=by
  obtain ⟨N₁,hN₁⟩:=first_vortex_class_assignment_from_rows_no_marked_budget α lam₀ d hα hlam₀ hd
  obtain ⟨N₂,hN₂⟩:=long_approximate_residual_matching_margins lam₀ hlam₀ d
  refine ⟨max N₁ N₂,?_⟩
  intro n hnN U C _ _ _ _ P S₀ S Del Used Sel Dv mv β ε Q π D σE t Jret b ρ₀ θ lam ξ C₀ u Old Pack g j R rate γ δloss raw T Src q φ M hUsed hγ hDel hsmall hδloss hmatch hn hU hρ₀ hb hbsmall hαb hSP hedit hξdeg hξedges hPack hS₀ hSelected hθ hθhi hC hehi hlamhi hu huhi hrow hε hOld hUlo hεsmall herror hpair hUhi
  have hn₁:N₁≤n:=(le_max_left _ _).trans hnN
  have hn₂:N₂≤n:=(le_max_right _ _).trans hnN
  have hApprox:=hN₂ n hn₂ U C
  have hdec:instDecidableEqFin n=firstClassIncidenceFinNoMarked n:=Subsingleton.elim _ _
  try rw [hdec] at hApprox
  have hB:∀v∈Q.extendedVertices 1,((longPhysicalStateGraph P σE {2,3}\Used).degree v:ℝ)≤lam₀*n:=by
    intro v hv
    rw [hUsed]
    exact hApprox P Del π σE g j R rate γ δloss hγ hUhi hDel hsmall hδloss M hmatch v
  exact hN₁ n hn₁ P S₀ S Del Used Sel Dv mv β ε Q π D σE t Jret b ρ₀ θ lam ξ C₀ u Old Pack
    hn hU hρ₀ hb hbsmall hαb hSP hedit hξdeg hξedges hPack hS₀ hSelected hθ hθhi hC hehi hlamhi hu huhi hrow hB hε hOld hUlo hεsmall herror hpair hUhi
end Oberwolfach
