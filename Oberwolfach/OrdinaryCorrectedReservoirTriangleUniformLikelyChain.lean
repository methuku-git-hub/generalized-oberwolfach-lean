module

public import Oberwolfach.OrdinaryTriangleLikelyCertificateSeparateCosts
public import Oberwolfach.OrdinaryCorrectedReservoirTwoStepUniformWheelChain
public import Oberwolfach.OrdinaryTriangleLikelyCoverCertificate
public import Oberwolfach.OrdinaryTriangleUniformHistoryCertificateAdapter

@[expose] public section
/-! The sharp triangle certificates feed the two-step uniform-history chain
using the same corrected reservoir and its terminal absorber. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_corrected_reservoir_triangle_uniform_likely_chain
    (P Q F:SimpleGraph V) (H:V→U→Prop) (D mv:ℕ) (β ε:ℝ) (Vort:Vortex U P D β ε mv)
    (m t a b:ℕ) (ξ:ℝ) (A Z Wterm:Finset V) (Bterm B:Finset U)
    (K:Finset (Sym2 V⊕(V×U))) (JQ:SimpleGraph V) (JH:V→U→Prop)
    (hw:OrdinaryCorrectedProtectedReservoirWitness 3 m t a b ξ Q F H A Z Wterm Bterm B K JQ JH)
    (hsize:Wterm.card+Bterm.card≤m) (L:ℕ) (hL:0<L) (cost deepCost:ℕ→ℝ)
    (hc:∀i,0≤cost i) (hd:∀i,0≤deepCost i)
    (hW:Vort.extendedVertices L=Wterm) (hB:Vort.extendedIndices L=Bterm):
    let Qcorr:=Q\JQ;let Hcorr:=fun v u=>H v u∧¬JH v u;
    let X:=fun k=>Vort.extendedVertices (k+1);let T:=fun k=>Vort.extendedVertices (k+2);
    let Zs:=fun k=>Vort.extendedIndices (k+1);let Ws:=fun k=>Vort.extendedIndices (k+2);
    let Gstart:=Qcorr\ordinaryResourceRim Qcorr K;
    let Hstart:=fun v u=>Hcorr v u∧¬(Sum.inr (v,u)∈K);
    (∀i,i<L→∀S (G:SimpleGraph V) (Hs:V→U→Prop),
      OrdinaryUniformProtectedBalanceHistory Gstart Hstart X T Zs Ws cost deepCost 3 i L S
        (fun t=>Vort.extendedVertices (t+2)) (fun t=>Vort.extendedVertices (t+1)) (fun t=>Vort.extendedIndices (t+2))
        (fun t=>Finset.Icc (t+3-2) t) (fun _ _=>0) (fun _ _=>0)→
      ordinaryHostResources G Hs=S→G≤Qcorr→(∀v u,Hs v u→Hcorr v u)→
      (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
      (∀u,3∣(Finset.univ.filter (fun v=>Hs v u)).card)→
      let f:=markedVortexVertexEmbedding Vort i;let g:=markedVortexHubEmbedding Vort i;
      OrdinaryTriangleLikelyCoverCertificate (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u))
        (markedVortexInnerVertices Vort i) (ordinaryVortexBufferedVertices Vort i 2)
        (markedVortexInnerHubs Vort i) (ordinaryVortexBufferedHubs Vort i 2) (cost i) (deepCost i))→
    HasOrdinaryWheelDecomposition Qcorr Hcorr 3 :=by
  intro Qcorr Hcorr X T Zs Ws Gstart Hstart hcert
  have hsep:=ordinary_triangle_uniform_history_certificate_adapter P F Gstart Qcorr Hstart Hcorr D mv β ε Vort L cost deepCost hcert
  exact ordinary_corrected_reservoir_two_step_uniform_wheel_chain P Q F H D mv β ε Vort 3 m t a b ξ
    A Z Wterm Bterm B K JQ JH hw hsize L hL cost deepCost hc hd hW hB
    (by convert hsep using 1 <;> congr! 12 <;> exact Subsingleton.elim _ _)
end Oberwolfach
