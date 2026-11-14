module

public import Oberwolfach.OrdinaryInitialProfileBothBalancesFromSample
public import Oberwolfach.OrdinaryTrackedComplementInitialVortexInputs
public import Oberwolfach.OrdinaryInitialMatchingMarginsAt
public import Oberwolfach.OrdinaryInitialCostToInner

@[expose] public section
/-! The original matching remainder, sampled row and inner-hub tests yield
an initial cleanup profile on the same edited target and reservoir. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_tracked_initial_both_balances_from_sample {n q mWheel mAbs t aAbs bAbs:ℕ}
    (P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q→SimpleGraph (Fin n)) (hFs:∀u,(Fs u).IsRegularOfDegree 2)
    (C:∀u,Finset (Fs u).ConnectedComponent) (hsize:∀u (c:↥(C u)),Fintype.card c.val=mWheel+1)
    (hS:S.IsRegularOfDegree (2*q)) (hSP:S≤P)
    (Inner Z Wterm A:Finset (Fin n)) (Hubs Bprotect Bterm:Finset (Fin q)) (ξ:ℝ)
    (K:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→Fin q→Prop)
    (cost:ℝ) (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (D mv mEdit Nedit:ℕ) (β ε θ α ρ₀ pmin hmin bal cBoundary δ ηedit ηBudget ζcert capHub:ℝ)
    (Vor:Vortex (Fin q) P D β ε mv) (hπ:∀i x,π x∈Vor.extendedVertices i↔x∈Vor.extendedVertices i)
    (hn:0<n) (hN:Nedit≤n) (hmEdit:mEdit≤mv) (hmv:0<mv) (hε:0<ε)
    (hreg:P.IsRegularOfDegree D) (hhalf:(n:ℝ)/2≤D) (hρ₀:0<ρ₀)
    (hρlo:ρ₀≤ initialIndexDensity (Fin q) D) (hρhi:initialIndexDensity (Fin q) D≤1)
    (hβ:0≤β) (hβα:β≤2*α) (hθ:1/2≤θ) (hdegree:(θ+α)*(n:ℝ)≤D)
    (hηle:ηBudget≤ηedit) (hζ:0≤ζcert) (hζcap:ζcert≤capHub)
    (hsmall:15*ηBudget≤ζcert*ε/2) (hcost0:0≤cost) (hcost:cost≤14*ηBudget*n)
    (hconf:cost+2*((3*d:ℕ):ℝ)≤15*ηBudget*n)
    (hMargins:OrdinaryInitialMatchingMarginsAt ρ₀ α pmin hmin ε bal cBoundary δ ηedit β d mEdit Nedit)
    (pR pH εR εH βe βh b Bweight ηHub:ℝ) (sp:Fin q→Bool→ℝ)
    (hpR:pmin≤pR) (hpR1:pR≤1) (hpH:hmin≤pH) (hpR0:0≤pR) (hpH0:0≤pH)
    (hεR:0≤εR) (hεRδ:εR≤δ) (hεH:0≤εH) (hεHδ:εH≤δ)
    (hβe:0≤βe) (hβecap:βe≤cBoundary*ε) (hβh:0≤βh) (hβhcap:βh≤cBoundary*ε)
    (hpEq:pR=initialIndexDensity (Fin q) D*pH) (hsp:∀u,sp u false=pH):
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (σ e)
    let Bad:=permutationConflictGraph π (3*d)
    let Reference:=rawWheelGraph P raw\Bad
    let Href:=rawWheelSpokes π d raw false
    let Q:=S\ordinaryEmbeddedComplements Fs C f
    let H:=fun v u=>v∉Set.range (f u)
    let Gstart:=Q\ordinaryResourceRim Q K
    let Hstart:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K)
    let I:=markedVortexInnerVertices Vor 0;let B:=markedVortexInnerHubs Vor 0;
    let fv:=markedVortexVertexEmbedding Vor 0;let gu:=markedVortexHubEmbedding Vor 0;
    let ρ:=markedVortexPermutation Vor π hπ 0;let rawLocal:=ordinaryRawRestrictPair fv gu raw;
    let Gloc:=Gstart.comap fv;let Floc:=Bad.comap fv;let Hloc:=fun v u=>Hstart (fv v) (gu u);
    let L:=cost+2*((3*d:ℕ):ℝ);
    OrdinaryCorrectedProtectedReservoirWitness (mWheel+1) mAbs t aAbs bAbs ξ Reference Bad Href
      A Z Wterm Bterm Bprotect K JQ JH→
    OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs K cost f→
    OrdinaryFixedVortexRowIndexEvent 3 d εR εH P Bad D mv β ε Vor π hπ pR pH sp false raw→
    OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P Bad D mv β ε Vor π hπ pR pH sp false raw→
    OrdinaryUniformInnerHubEvent mWheel P D mv d β ε Vor π hπ pR pH βe βh b Bweight ηHub capHub
      (fun _=>θ+α-β/2) (fun k=>εR*(markedVortexInnerVertices Vor k).card)
      (fun k=>εH*(markedVortexInnerHubs Vor k).card) sp false raw→
    Gstart≤P\Bad ∧
    (∀v,Gstart.degree v=2*(Finset.univ.filter (Hstart v)).card) ∧
    (∀u,(mWheel+1)∣(Finset.univ.filter (fun v=>Hstart v u)).card) ∧
    L≤ζcert*I.card ∧
    (∀w:markedVortexVertexType Vor 0⊕markedVortexHubType Vor 0,
      ((changed ((ordinaryPhysicalGraph (rawWheelGraph (P.comap fv) rawLocal) (rawWheelSpokes ρ d rawLocal false)).neighborFinset w)
        ((ordinaryPhysicalGraph Gloc Hloc).neighborFinset w)).card:ℝ)≤L) ∧
    OrdinaryCleanupParentProfiles (P.comap fv) Gloc Floc Hloc ρ d I B pR pH (θ+α-β/2)
      (εR*I.card) (εH*B.card) L βe βh (fun u=>sp (gu u)) false rawLocal ∧
    (∀v:I,|((Gloc.induce (I:Set _)).degree v:ℝ)-2*(Finset.univ.filter (fun u:B=>Hloc v.val u.val)).card|≤bal*I.card) ∧
    (∀v∉I,|((Gloc.neighborFinset v∩I).card:ℝ)-2*(B.filter (Hloc v)).card|≤bal*I.card) ∧
    (∀v,|((Gloc.neighborFinset v∩ordinaryVortexBufferedVertices Vor 0 2).card:ℝ)-
      2*((ordinaryVortexBufferedHubs Vor 0 2).filter (Hloc v)).card|≤
      (initialIndexDensity (Fin q) D*pH)*β*(ordinaryVortexBufferedVertices Vor 0 2).card+
        εR*(ordinaryVortexBufferedVertices Vor 0 2).card+2*(εH*(ordinaryVortexBufferedHubs Vor 0 2).card)+3*L) ∧
    Nonempty (OrdinaryMixedHubWeightsInnerScale mWheel b Bweight ηHub Gloc Floc Hloc I B) :=by
  intro raw Bad Reference Href Q H Gstart Hstart I B fv gu ρ rawLocal Gloc Floc Hloc L hw hf hrow htwo hfamily
  have hQP:Q≤P:=sdiff_le.trans hSP
  obtain ⟨hhost,hbal,hdiv,hphys⟩:=ordinary_tracked_complement_initial_vortex_inputs P S π d σ Fs hFs C hsize hS
    Inner Z Wterm A Hubs Bprotect Bterm ξ K JQ JH cost f D mv β ε Vor hπ hw hf hQP
  have hcostEdit:cost≤14*ηedit*n:=by
    have hn0:(0:ℝ)≤n:=by positivity
    nlinarith [mul_nonneg (show 0≤ηedit-ηBudget by linarith) hn0]
  have hmarg:=hMargins hN hn hmEdit P Vor hreg hhalf hρlo hρhi pR pH θ εR εH βe βh cost
    hpR hpR1 hpH hθ hεR hεRδ hεH hεHδ hβe hβecap hβh hβhcap hpEq hcost0 hcostEdit
  have hL0:0≤L:=by dsimp [L]; positivity
  have hLζ:L≤ζcert*I.card:=ordinary_initial_cost_to_inner P D mv β ε Vor hε hmv ηBudget ζcert L hζ hsmall
    (by simpa only [Fintype.card_fin] using hconf)
  have hLcap:L≤capHub*I.card:=hLζ.trans (mul_le_mul_of_nonneg_right hζcap (by positivity))
  have hprofile:=ordinary_initial_profile_both_balances_from_sample mWheel d P Gstart Hstart D mv
    β ε θ α pR pH εR εH L βe βh bal b Bweight ηHub capHub Vor π hπ sp false raw
    (by simpa only [Fintype.card_fin] using hn) hreg (hρ₀.trans_le hρlo) hβ hpR0 hpR1 hpH0 hεR hεH hL0
    hθ hβα (by simpa only [Fintype.card_fin] using hdegree) hpEq hsp hhost hrow hfamily htwo hLcap
    (by intro w;convert hphys w using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    hmarg.1 hmarg.2.1 hmarg.2.2
  refine ⟨hhost,hbal,hdiv,hLζ,?_,?_⟩
  · intro w;convert hphys w using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · obtain ⟨hp,hnear,hcross,hdeep,hweight⟩:=hprofile
    refine ⟨?_,?_,?_,?_,?_⟩
    · convert hp using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
    · intro v;convert hnear v using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
    · intro v hv;convert hcross v hv using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
    · intro v;convert hdeep v using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
    · convert hweight using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
end Oberwolfach
