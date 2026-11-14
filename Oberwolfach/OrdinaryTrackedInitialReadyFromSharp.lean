module

public import Oberwolfach.OrdinaryTrackedInitialCertificateReady
public import Oberwolfach.OrdinaryVortexInitialReadyFromSharp

@[expose] public section
/-! The tracked matching remainder and corrected reservoir supply the
initial wheel interface in the form used by the sampled sharp reference. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_tracked_initial_ready_from_sharp {n q mAbs t aAbs bAbs:ℕ}
    (s:OrdinaryVortexFineCertificateParametersGeneralLoad) (hcert:OrdinaryVortexFineCertificateAtGeneralLoad s)
    (P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Fs:Fin q→SimpleGraph (Fin n)) (hFs:∀u,(Fs u).IsRegularOfDegree 2)
    (C:∀u,Finset (Fs u).ConnectedComponent) (hsize:∀u (c:↥(C u)),Fintype.card c.val=s.m+1)
    (hS:S.IsRegularOfDegree (2*q)) (hSP:S≤P)
    (Inner Z Wterm A:Finset (Fin n)) (Hubs B Bterm:Finset (Fin q)) (ξ:ℝ)
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
    OrdinaryCorrectedProtectedReservoirWitness (s.m+1) mAbs t aAbs bAbs ξ Reference Bad Href
      A Z Wterm Bterm B K JQ JH→
    OrdinaryTrackedComplementFor P S π d σ Fs C Inner Hubs K cost f→
    OrdinaryVortexInitialReadyFromSharpAt s hcert P Gstart D mv β ε Vor π hπ d raw Hstart ∧
    let fv:markedVortexVertexType Vor 0↪Fin n:=(markedVortexVertexEmbedding Vor 0).toEmbedding
    let gu:=markedVortexHubEmbedding Vor 0;let ρ:=markedVortexPermutation Vor π hπ 0
    let rawLocal:=ordinaryRawRestrictPair fv gu raw;
    ∀w:markedVortexVertexType Vor 0⊕markedVortexHubType Vor 0,
      ((changed ((ordinaryPhysicalGraph (rawWheelGraph (P.comap fv) rawLocal)
        (rawWheelSpokes ρ d rawLocal false)).neighborFinset w)
        ((ordinaryPhysicalGraph (Gstart.comap fv) (fun v u=>Hstart (fv v) (gu u))).neighborFinset w)).card:ℝ)≤
        cost+2*((3*d:ℕ):ℝ) :=by
  intro raw Bad Reference Href Q H Gstart Hstart hw hf
  have h:=ordinary_tracked_initial_certificate_ready s hcert P S π d σ Fs hFs C hsize hS hSP
    Inner Z Wterm A Hubs B Bterm ξ K JQ JH cost f D mv β ε Vor hπ hw hf
  exact ⟨ordinary_vortex_initial_ready_from_sharp s hcert P Gstart D mv β ε Vor π hπ d raw Hstart h.1,h.2⟩
end Oberwolfach
