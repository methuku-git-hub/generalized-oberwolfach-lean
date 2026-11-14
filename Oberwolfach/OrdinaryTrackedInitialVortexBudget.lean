module

public import Oberwolfach.OrdinaryTrackedComplementInitialVortexInputs
public import Oberwolfach.OrdinaryInitialConflictBudgetEventually
public import Oberwolfach.OrdinaryInitialCostToInner

@[expose] public section
/-! The same matching remainder and fixed absorber give the initial vortex
inputs within any prescribed inner-level edit cap, for large order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_tracked_initial_vortex_budget_eventually
    (d:ℕ) (η ζ ε:ℝ) (hη:0<η) (hζ:0≤ζ) (hε:0<ε) (hsmall:15*η≤ζ*ε/2):
    ∃N:ℕ,∀{n q r mAbs t aAbs bAbs:ℕ},N≤n→
    ∀(P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q→SimpleGraph (Fin n)) (hFs:∀u,(Fs u).IsRegularOfDegree 2)
    (C:∀u,Finset (Fs u).ConnectedComponent) (hsize:∀u (c:↥(C u)),Fintype.card c.val=r)
    (hS:S.IsRegularOfDegree (2*q)) (Inner Z Wterm A:Finset (Fin n)) (Hubs B Bterm:Finset (Fin q)) (ξ:ℝ)
    (K:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→Fin q→Prop)
    (cost:ℝ) (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (D mv:ℕ) (hm:0<mv) (β:ℝ) (Vor:Vortex (Fin q) P D β ε mv)
    (hπ:∀i x,π x∈Vor.extendedVertices i↔x∈Vor.extendedVertices i),
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (σ e)
    let Bad:=permutationConflictGraph π (3*d)
    let Reference:=rawWheelGraph P raw\Bad
    let Href:=rawWheelSpokes π d raw false
    let Q:=S\ordinaryEmbeddedComplements Fs C f
    let H:=fun v u=>v∉Set.range (f u)
    let Gstart:=Q\ordinaryResourceRim Q K
    let Hstart:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K);
    OrdinaryCorrectedProtectedReservoirWitness r mAbs t aAbs bAbs ξ Reference Bad Href
      A Z Wterm Bterm B K JQ JH→
    OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs K cost f→ Q≤P→cost≤14*η*n→
    Gstart≤P\Bad ∧
    (∀v,Gstart.degree v=2*(Finset.univ.filter (Hstart v)).card) ∧
    (∀u,r∣(Finset.univ.filter (fun v=>Hstart v u)).card) ∧
    let fv:markedVortexVertexType Vor 0↪Fin n:=(markedVortexVertexEmbedding Vor 0).toEmbedding
    let gu:=markedVortexHubEmbedding Vor 0;let ρ:=markedVortexPermutation Vor π hπ 0
    let rawLocal:=ordinaryRawRestrictPair fv gu raw;
    ∀w:markedVortexVertexType Vor 0⊕markedVortexHubType Vor 0,
      ((changed ((ordinaryPhysicalGraph (rawWheelGraph (P.comap fv) rawLocal)
        (rawWheelSpokes ρ d rawLocal false)).neighborFinset w)
        ((ordinaryPhysicalGraph (Gstart.comap fv) (fun v u=>Hstart (fv v) (gu u))).neighborFinset w)).card:ℝ)≤
        ζ*(markedVortexInnerVertices Vor 0).card :=by
  obtain ⟨N,hN⟩:=ordinary_initial_conflict_budget_eventually d η hη
  refine ⟨N,?_⟩
  intro n q r mAbs t aAbs bAbs hn P S π σ Fs hFs C hsize hS Inner Z Wterm A Hubs B Bterm ξ K JQ JH cost f D mv hm β Vor hπ
    raw Bad Reference Href Q H Gstart Hstart hw hf hQP hcost
  have hc:=hN n hn cost hcost
  have hscaled:=ordinary_initial_cost_to_inner P D mv β ε Vor hε hm η ζ (cost+2*((3*d:ℕ):ℝ)) hζ hsmall
    (by simpa only [Fintype.card_fin] using hc)
  obtain ⟨hhost,hbal,hdiv,hphysical⟩:=ordinary_tracked_complement_initial_vortex_inputs P S π d σ Fs hFs C hsize hS
    Inner Z Wterm A Hubs B Bterm ξ K JQ JH cost f D mv β ε Vor hπ hw hf hQP
  refine ⟨hhost,hbal,hdiv,?_⟩
  intro fv gu ρ rawLocal w
  exact (hphysical w).trans hscaled
end Oberwolfach
