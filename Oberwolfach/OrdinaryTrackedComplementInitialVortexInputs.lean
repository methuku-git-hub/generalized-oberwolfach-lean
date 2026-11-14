module

public import Oberwolfach.OrdinaryTrackedComplementInitialHost
public import Oberwolfach.OrdinaryVortexInitialPhysicalEditFromReference

@[expose] public section
/-! The same matching remainder and corrected absorber provide the host,
exact balance, divisibility and physical edit for the initial vortex step. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_tracked_complement_initial_vortex_inputs {n q r mAbs t aAbs bAbs:ℕ}
    (P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q→SimpleGraph (Fin n)) (hFs:∀u,(Fs u).IsRegularOfDegree 2)
    (C:∀u,Finset (Fs u).ConnectedComponent) (hsize:∀u (c:↥(C u)),Fintype.card c.val=r)
    (hS:S.IsRegularOfDegree (2*q)) (Inner Z Wterm A:Finset (Fin n)) (Hubs B Bterm:Finset (Fin q)) (ξ:ℝ)
    (K:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→Fin q→Prop)
    (cost:ℝ) (f:∀u,{x:Fin n // (Fs u).connectedComponentMk x∉C u}↪Fin n)
    (D mv:ℕ) (β ε:ℝ) (Vor:Vortex (Fin q) P D β ε mv)
    (hπ:∀i x,π x∈Vor.extendedVertices i↔x∈Vor.extendedVertices i):
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
    OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs K cost f→ Q≤P→
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
        cost+2*((3*d:ℕ):ℝ) :=by
  intro raw Bad Reference Href Q H Gstart Hstart hw hf hQP
  obtain ⟨hhost,hbal,hdiv,hphysical⟩:=ordinary_tracked_complement_initial_host P S π d σ Fs hFs C hsize hS
    Inner Z Wterm A Hubs B Bterm ξ K JQ JH cost f hw hf hQP
  have hLF:0≤(2*((3*d:ℕ):ℝ)):=by positivity
  have hF:∀v,(Bad.degree v:ℝ)≤2*((3*d:ℕ):ℝ):=by
    intro v
    dsimp [Bad]
    exact_mod_cast permutationConflictGraph_degree_le π (3*d) v
  have hlocal:=ordinary_vortex_initial_physical_edit_from_reference P Bad Gstart Hstart D mv β ε Vor π hπ d false raw
    cost (2*((3*d:ℕ):ℝ)) hLF hF
    (by intro w;convert hphysical w using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
  refine ⟨hhost,hbal,hdiv,?_⟩
  intro fv gu ρ rawLocal w
  convert hlocal w using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
