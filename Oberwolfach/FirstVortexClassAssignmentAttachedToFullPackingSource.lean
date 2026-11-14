module

public import Oberwolfach.LongSelectedOrientedEarlyAttachFullPacking
public import Oberwolfach.FirstVortexClassAssignmentFromCommonIncidenceNoMarkedBudget
public import Oberwolfach.LongSelectedOrientedEarlyAttachExactOld

@[expose] public section
/-! Attach the class-specific, no-marked-budget assignment to the actual
residual source built from the same surviving approximate matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstClassOrientedFullPackingAttachSourceFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n
local instance (priority := 2000) firstClassOrientedFullPackingAttachSourceSix : DecidableEq (Fin 6) := instDecidableEqFin 6

theorem first_vortex_class_assignment_attached_to_full_packing_source
    (α lam₀:ℝ) (d:ℕ) (hα:0<α) (hlam₀:0<lam₀) (hd:1≤d):
    ∃N:ℕ,∀n:ℕ,N≤n→∀ {U:Type} [Fintype U] [DecidableEq U]
    (P S₀ S Del Used Sel:SimpleGraph (Fin n)) (Dv mv:ℕ) (β ε:ℝ)
    (Q:Vortex U P Dv β ε mv) (π:Equiv.Perm (Fin n)) (D:Fin n→Fin n→Prop)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t)
    (b ρ₀ θ lam ξ C₀ u:ℝ) (K m:ℕ) (ℓ:Fin K→ℕ) (rate γ δloss:ℝ),
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σE e)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let Src:=longRawSurvivingResources P π d raw true true Del.edgeFinset
    let R:=mixedCandidateResources (longRawHubResources (U:=U) π d m ℓ)
    let q:=survivingCandidateEmbedding R Src T (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw true true
    let Kbad:=longRequiredPhysicalGraph S (S\Used) Sel π d (Q.extendedVertices 1) D (fun x y=>Used.Adj x y);
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈Src))))
    (hUsed:Used=physicalRimCandidateUnion φ (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (M.map q))
    (hdisj:∀c∈M,∀c'∈M,c≠c'→Disjoint
      (restrictedResourceSet R (Function.Embedding.subtype (·∈Src)) c)
      (restrictedResourceSet R (Function.Embedding.subtype (·∈Src)) c'))
    (hγ:0≤γ) (hDel:∀x,(Del.degree x:ℝ)≤δloss)
    (hsmall:2*max rate (4*γ)≤lam₀/3) (hδloss:δloss≤(lam₀/3)*n)
    (hmatch:∀i,((longRawIncidenceSet Src i\M.biUnion (restrictedResourceSet R (Function.Embedding.subtype (·∈Src)))).card:ℝ)≤
      max (rate*n) (γ*(longRawIncidenceSet Src i).card))
    (hn:0<n) (hU:0<Fintype.card U) (hρ₀:0<ρ₀) (hb:0≤b)
    (hbsmall:b≤((ρ₀/4)/40000)/16) (hαb:α/16≤b)
    (hSP:S≤P) (hedit:∀v,((changed (S₀.neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)
    (hξdeg:ξ≤α/32) (hξedges:ξ/2≤(lam-lam₀)*ε)
    (hS₀:S₀=longPhysicalStateGraph P σE {0,1,2,3,4})
    (hSelected:∀x∈Q.extendedVertices 1,∀y∈Q.extendedVertices 1,
      (longSelectedPhysicalGraph P π d σE).Adj x y→Sel.Adj x y)
    (hθ:0≤θ) (hθhi:θ≤1/100) (hC:1≤C₀) (hehi:ε≤(α/2)/(1000*C₀))
    (hlamhi:lam₀≤(α/2)/128) (hu:0≤u) (huhi:u≤2*θ)
    (hrow:∀v∈Q.extendedVertices 1,
      |(((P.neighborFinset v∩Q.extendedVertices 1).filter (fun w=>(σE (Sum.inl s(v,w))).1=4)).card:ℝ)-
        u*(P.neighborFinset v∩Q.extendedVertices 1).card|<(n:ℝ)^(3/4:ℝ))
    (hε:0≤ε) (hUlo:(ρ₀/4)*n≤Fintype.card U) (hεsmall:ε≤(ρ₀/4)/80000)
    (herror:(n:ℝ)^(3/4:ℝ)≤(ρ₀/4)*n/80000)
    (hpair:∀x y,x≠y→(5/8:ℝ)*(1/100:ℝ)^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
      (((Finset.univ:Finset U).filter (fun w=>rawIntervalFamilyState π d
        (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) (x,w)=some (Sum.inr false) ∧
        rawIntervalFamilyState π d (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) (y,w)=some (Sum.inr false))).card:ℝ))
    (hUhi:Fintype.card U≤n) (F:U→SimpleGraph (Fin n)) (absorber:U→Finset (Fin n)) (δlocal:ℝ),
    LongSelectedExactOrientedSourceWithLoad hU F P π d m ℓ raw t Jret σE
      (Q.extendedIndices 1) (Q.extendedVertices 1) Kbad absorber δlocal (M.map q)→
    LongSelectedOrientedSourceExactOld hU F P π d m ℓ raw t Jret σE
      (Q.extendedIndices 1) (Q.extendedVertices 1) Kbad Used absorber δlocal
      (fun Old Pack=>FirstVortexClassPrescribedAssignmentNoMarkedBudget P S Del Used Kbad
        (Q.extendedVertices 1) π d σE t Jret (Q.extendedIndices 1) α b ρ₀ θ ε lam Old Pack ∧ Pack=Used.edgeFinset) (M.map q):=by
  obtain ⟨N,hN⟩:=first_vortex_class_assignment_from_common_incidence_no_marked_budget α lam₀ d hα hlam₀ hd
  refine ⟨N,?_⟩
  intro n hnN U _ _ P S₀ S Del Used Sel Dv mv β ε Q π D σE t Jret b ρ₀ θ lam ξ C₀ u K m ℓ rate γ δloss raw T Src R q φ Kbad M hUsed hdisj hγ hDel hsmall hδloss hmatch hn hU hρ₀ hb hbsmall hαb hSP hedit hξdeg hξedges hS₀ hSelected hθ hθhi hC hehi hlamhi hu huhi hrow hε hUlo hεsmall herror hpair hUhi F absorber δlocal hsource
  letI : DecidableEq (Σ i:Option (Fin K),longRawHubCandidates (U:=U) π d m ℓ i) := Classical.decEq _
  have hN':=hN n hnN (U:=U) (C:=Σ i:Option (Fin K),longRawHubCandidates (U:=U) π d m ℓ i)
  have hdec:firstClassIncidenceFinNoMarked n=firstClassOrientedFullPackingAttachSourceFin n:=Subsingleton.elim _ _
  have hdec6:firstClassIncidenceSixNoMarked=firstClassOrientedFullPackingAttachSourceSix:=Subsingleton.elim _ _
  have hdecK:selectedOrientedEarlyAttachFullPackingFin K=firstClassOrientedFullPackingAttachSourceFin K:=Subsingleton.elim _ _
  have hdecA:selectedOrientedEarlyAttachFullPackingFin n=firstClassOrientedFullPackingAttachSourceFin n:=Subsingleton.elim _ _
  try rw [hdec] at hN'
  try rw [hdec6] at hN'
  have hAttach:=long_selected_oriented_early_source_attach_full_packing_assignment hU F P Del π d m ℓ σE t Jret
    (Q.extendedIndices 1) (Q.extendedVertices 1) Kbad absorber δlocal
    (FirstVortexClassPrescribedAssignmentNoMarkedBudget P S Del Used Kbad
      (Q.extendedVertices 1) π d σE t Jret (Q.extendedIndices 1) α b ρ₀ θ ε lam)
  try rw [hdecK] at hAttach
  try rw [hdecA] at hAttach
  have hAttach':=hAttach M
  dsimp only at hAttach'
  dsimp only [R,raw,T,Src,q,φ,longRawHubResources] at hUsed
  rw [←hUsed] at hAttach'
  apply hAttach' hsource hdisj
  intro Old Pack hOld hPack
  exact hN' P S₀ S Del Used Sel Dv mv β ε Q π D σE t Jret b ρ₀ θ lam ξ C₀ u Old Pack true true R rate γ δloss
    M hUsed hγ hDel hsmall hδloss hmatch hn hU hρ₀ hb hbsmall hαb hSP hedit hξdeg hξedges hPack hS₀ hSelected hθ hθhi hC hehi hlamhi hu huhi hrow hε hOld hUlo hεsmall herror hpair hUhi
end Oberwolfach
