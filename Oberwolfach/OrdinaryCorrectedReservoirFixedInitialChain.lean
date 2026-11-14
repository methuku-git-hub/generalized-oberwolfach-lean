module

public import Oberwolfach.OrdinaryCorrectedReservoirInitialLaterChain

@[expose] public section
/-! The initial host of a protected history is the actual corrected starting host.
One initial certificate and the later certificates therefore drive the chain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_corrected_reservoir_fixed_initial_later_chain
    (P Q F:SimpleGraph V) (H:V→U→Prop) (D mv:ℕ) (β ε:ℝ) (Vort:Vortex U P D β ε mv)
    (r m t a b:ℕ) (ξ:ℝ) (A Z Wterm:Finset V) (Bterm B:Finset U)
    (K:Finset (Sym2 V⊕(V×U))) (JQ:SimpleGraph V) (JH:V→U→Prop)
    (hw:OrdinaryCorrectedProtectedReservoirWitness r m t a b ξ Q F H A Z Wterm Bterm B K JQ JH)
    (hsize:Wterm.card+Bterm.card≤m) (L:ℕ) (hL:0<L) (cost deepCost:ℕ→ℝ)
    (hc:∀i,0≤cost i) (hd:∀i,0≤deepCost i)
    (hW:Vort.extendedVertices L=Wterm) (hB:Vort.extendedIndices L=Bterm):
    let Qcorr:=Q\JQ;let Hcorr:=fun v u=>H v u∧¬JH v u;
    let X:=fun k=>Vort.extendedVertices (k+1);let T:=fun k=>Vort.extendedVertices (k+2);
    let Zs:=fun k=>Vort.extendedIndices (k+1);let Ws:=fun k=>Vort.extendedIndices (k+2);
    let Gstart:=Qcorr\ordinaryResourceRim Qcorr K;
    let Hstart:=fun v u=>Hcorr v u∧¬(Sum.inr (v,u)∈K);
    (let f:=markedVortexVertexEmbedding Vort 0;let g:=markedVortexHubEmbedding Vort 0;
      OrdinaryWheelLikelySeparateCostsCertificate (Gstart.comap f) (F.comap f) (fun v u=>Hstart (f v) (g u))
        (markedVortexInnerVertices Vort 0) (ordinaryVortexBufferedVertices Vort 0 2)
        (markedVortexInnerHubs Vort 0) (ordinaryVortexBufferedHubs Vort 0 2) r (cost 0) (deepCost 0))→
    (∀i,i+1<L→∀S (G:SimpleGraph V) (Hs:V→U→Prop),
      OrdinaryUniformProtectedBalanceHistory Gstart Hstart X T Zs Ws cost deepCost r (i+1) L S
        (fun t=>Vort.extendedVertices (t+2)) (fun t=>Vort.extendedVertices (t+1)) (fun t=>Vort.extendedIndices (t+2))
        (fun t=>Finset.Icc (t+3-2) t) (fun _ _=>0) (fun _ _=>0)→
      ordinaryHostResources G Hs=S→G≤Qcorr→(∀v u,Hs v u→Hcorr v u)→
      (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
      (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card)→
      let f:=markedVortexVertexEmbedding Vort (i+1);let g:=markedVortexHubEmbedding Vort (i+1);
      OrdinaryWheelLikelySeparateCostsCertificate (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u))
        (markedVortexInnerVertices Vort (i+1)) (ordinaryVortexBufferedVertices Vort (i+1) 2)
        (markedVortexInnerHubs Vort (i+1)) (ordinaryVortexBufferedHubs Vort (i+1) 2) r (cost (i+1)) (deepCost (i+1)))→
    HasOrdinaryWheelDecomposition Qcorr Hcorr r :=by
  intro Qcorr Hcorr X T Zs Ws Gstart Hstart hInitial hLater
  apply ordinary_corrected_reservoir_initial_later_chain P Q F H D mv β ε Vort r m t a b ξ
    A Z Wterm Bterm B K JQ JH hw hsize L hL cost deepCost hc hd hW hB
  · intro S G Hs hhist hstate hG hH hbal hdiv
    have hq:ordinaryHistoryRim Gstart hhist.rim hhist.spokes 0=Gstart:=by
      ext x y
      simp [ordinaryHistoryRim,ordinaryDeletionHistory]
    have hh:ordinaryHistorySpokes Hstart hhist.rim hhist.spokes 0=Hstart:=by
      funext x u
      simp [ordinaryHistorySpokes,ordinarySpokesAfterPhysicalDeletion,ordinaryDeletionHistory]
    have he:=hhist.trace.1
    rw [hq,hh] at he
    obtain ⟨hge,hhe⟩:=ordinaryHostResources_injective G Gstart Hs Hstart (hstate.trans he.symm)
    subst G
    subst Hs
    exact hInitial
  · exact hLater
end Oberwolfach
