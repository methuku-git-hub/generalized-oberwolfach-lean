module

public import Oberwolfach.OrdinaryCorrectedReservoirNamedWitness
public import Oberwolfach.OrdinaryVortexTwoStepUniformLocalWheelChain

@[expose] public section
/-! The very same corrected reservoir supplies the terminal absorber and
the pre-reserved wheels for the buffered uniform level chain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 35000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_corrected_reservoir_two_step_uniform_wheel_chain
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
    (∀i,i<L→∀S (G:SimpleGraph V) (Hs:V→U→Prop),
      OrdinaryUniformProtectedBalanceHistory Gstart Hstart X T Zs Ws cost deepCost r i L S
        (fun t=>Vort.extendedVertices (t+2)) (fun t=>Vort.extendedVertices (t+1)) (fun t=>Vort.extendedIndices (t+2))
        (fun t=>Finset.Icc (t+3-2) t) (fun _ _=>0) (fun _ _=>0)→
      ordinaryHostResources G Hs=S→G≤Qcorr→(∀v u,Hs v u→Hcorr v u)→
      (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
      (∀u,r∣(Finset.univ.filter (fun v=>Hs v u)).card)→
      let f:=markedVortexVertexEmbedding Vort i;let g:=markedVortexHubEmbedding Vort i;
      OrdinaryWheelLikelySeparateCostsCertificate (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u))
        (markedVortexInnerVertices Vort i) (ordinaryVortexBufferedVertices Vort i 2)
        (markedVortexInnerHubs Vort i) (ordinaryVortexBufferedHubs Vort i 2) r (cost i) (deepCost i))→
    HasOrdinaryWheelDecomposition Qcorr Hcorr r :=by
  intro Qcorr Hcorr X T Zs Ws Gstart Hstart hcert
  rcases hw with ⟨hK,hdis,hrows,hhubs,hrowSub,hdec,hres,hJQ,hJQfree,hJHfree,hKcorr,hbal,hdiv,hJQdeg,hJHdeg⟩
  exact ordinary_vortex_two_step_uniform_separate_cost_wheel_likely_chain P D mv β ε Vort Qcorr Q F Hcorr H r m
    Wterm Bterm hsize (by intro v;convert hbal v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro u;convert hdiv u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) (show Qcorr≤Q from sdiff_le) (by intro v u hvu;exact hvu.1)
    K hKcorr hdec hres L hL cost deepCost hc hd hW hB hcert
end Oberwolfach
