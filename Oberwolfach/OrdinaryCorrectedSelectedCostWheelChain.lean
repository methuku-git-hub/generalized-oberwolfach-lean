module

public import Oberwolfach.OrdinaryCorrectedReservoirFixedInitialChain
public import Oberwolfach.OrdinaryVortexSelectedCostSchedule

@[expose] public section
/-! Apply the protected absorber chain with the actual wheel certificate's
selected cost and fine-cover boundary cost at each level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_corrected_selected_cost_wheel_chain
    (P Q F:SimpleGraph V) (H:V→U→Prop) (D mv:ℕ) (β ε:ℝ) (Vor:Vortex U P D β ε mv)
    (r m t a b:ℕ) (ξ:ℝ) (A Z Wterm:Finset V) (Bterm B:Finset U)
    (K:Finset (Sym2 V⊕(V×U))) (JQ:SimpleGraph V) (JH:V→U→Prop)
    (hw:OrdinaryCorrectedProtectedReservoirWitness r m t a b ξ Q F H A Z Wterm Bterm B K JQ JH)
    (hsize:Wterm.card+Bterm.card≤m) (L:ℕ) (hL:0<L) (rate ξroot:ℝ) (hrate:0≤rate) (hξroot:0≤ξroot)
    (hW:Vor.extendedVertices L=Wterm) (hB:Vor.extendedIndices L=Bterm):
    let Qcorr:=Q\JQ;let Hcorr:=fun v u=>H v u∧¬JH v u;
    let X:=fun k=>Vor.extendedVertices (k+1);let T:=fun k=>Vor.extendedVertices (k+2);
    let Zs:=fun k=>Vor.extendedIndices (k+1);let Ws:=fun k=>Vor.extendedIndices (k+2);
    let Gstart:=Qcorr\ordinaryResourceRim Qcorr K;
    let Hstart:=fun v u=>Hcorr v u∧¬(Sum.inr (v,u)∈K);
    let cost:=ordinaryVortexSelectedCost Vor rate;let deepCost:=ordinaryFineDeepCost Vor ξroot;
    (let f:=markedVortexVertexEmbedding Vor 0;let g:=markedVortexHubEmbedding Vor 0;
      OrdinaryWheelLikelySeparateCostsCertificate (Gstart.comap f) (F.comap f) (fun v u=>Hstart (f v) (g u))
        (markedVortexInnerVertices Vor 0) (ordinaryVortexBufferedVertices Vor 0 2)
        (markedVortexInnerHubs Vor 0) (ordinaryVortexBufferedHubs Vor 0 2) r
        (rate*Fintype.card (markedVortexVertexType Vor 0⊕markedVortexHubType Vor 0))
        (10*ξroot*(markedVortexInnerVertices Vor 0).card))→
    (∀i,i+1<L→∀S (G:SimpleGraph V) (Hs:V→U→Prop),
      OrdinaryUniformProtectedBalanceHistory Gstart Hstart X T Zs Ws cost deepCost r (i+1) L S
        (fun t=>Vor.extendedVertices (t+2)) (fun t=>Vor.extendedVertices (t+1)) (fun t=>Vor.extendedIndices (t+2))
        (fun t=>Finset.Icc (t+3-2) t) (fun _ _=>0) (fun _ _=>0)→
      ordinaryHostResources G Hs=S→G≤Qcorr→(∀v u,Hs v u→Hcorr v u)→
      (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
      (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card)→
      let f:=markedVortexVertexEmbedding Vor (i+1);let g:=markedVortexHubEmbedding Vor (i+1);
      OrdinaryWheelLikelySeparateCostsCertificate (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u))
        (markedVortexInnerVertices Vor (i+1)) (ordinaryVortexBufferedVertices Vor (i+1) 2)
        (markedVortexInnerHubs Vor (i+1)) (ordinaryVortexBufferedHubs Vor (i+1) 2) r
        (rate*Fintype.card (markedVortexVertexType Vor (i+1)⊕markedVortexHubType Vor (i+1)))
        (10*ξroot*(markedVortexInnerVertices Vor (i+1)).card))→
    HasOrdinaryWheelDecomposition Qcorr Hcorr r :=by
  intro Qcorr Hcorr X T Zs Ws Gstart Hstart cost deepCost hInitial hLater
  obtain ⟨hc,hd,_,_⟩:=ordinary_vortex_selected_cost_schedule Vor rate ξroot 0 hrate hξroot (by norm_num)
  apply ordinary_corrected_reservoir_fixed_initial_later_chain P Q F H D mv β ε Vor r m t a b ξ
    A Z Wterm Bterm B K JQ JH hw hsize L hL cost deepCost hc hd hW hB
  · simpa [cost,deepCost,ordinaryVortexSelectedCost,ordinary_fine_deep_cost_at_level] using hInitial
  · intro i hi S G Hs hhist hstate hG hH hbal hdiv
    have hlocal:=hLater i hi S G Hs hhist hstate hG hH hbal hdiv
    simpa [cost,deepCost,ordinaryVortexSelectedCost,ordinary_fine_deep_cost_at_level] using hlocal
end Oberwolfach
