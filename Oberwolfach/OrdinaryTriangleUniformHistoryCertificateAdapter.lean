module

public import Oberwolfach.OrdinaryTriangleLikelyCertificateSeparateCosts
public import Oberwolfach.OrdinaryVortexTwoStepUniformLocalWheelChain

@[expose] public section
/-! Convert triangle likely certificates pointwise along one protected
uniform history, preserving both level costs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_triangle_uniform_history_certificate_adapter
    (P F Gstart Qcorr:SimpleGraph V) (Hstart Hcorr:V→U→Prop)
    (D mv:ℕ) (β ε:ℝ) (Vort:Vortex U P D β ε mv) (L:ℕ) (cost deepCost:ℕ→ℝ):
    let X:=fun k=>Vort.extendedVertices (k+1);let T:=fun k=>Vort.extendedVertices (k+2);
    let Zs:=fun k=>Vort.extendedIndices (k+1);let Ws:=fun k=>Vort.extendedIndices (k+2);
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
    (∀i,i<L→∀S (G:SimpleGraph V) (Hs:V→U→Prop),
      OrdinaryUniformProtectedBalanceHistory Gstart Hstart X T Zs Ws cost deepCost 3 i L S
        (fun t=>Vort.extendedVertices (t+2)) (fun t=>Vort.extendedVertices (t+1)) (fun t=>Vort.extendedIndices (t+2))
        (fun t=>Finset.Icc (t+3-2) t) (fun _ _=>0) (fun _ _=>0)→
      ordinaryHostResources G Hs=S→G≤Qcorr→(∀v u,Hs v u→Hcorr v u)→
      (∀v,G.degree v=2*(Finset.univ.filter (Hs v)).card)→
      (∀u,3∣(Finset.univ.filter (fun v=>Hs v u)).card)→
      let f:=markedVortexVertexEmbedding Vort i;let g:=markedVortexHubEmbedding Vort i;
      OrdinaryWheelLikelySeparateCostsCertificate (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u))
        (markedVortexInnerVertices Vort i) (ordinaryVortexBufferedVertices Vort i 2)
        (markedVortexInnerHubs Vort i) (ordinaryVortexBufferedHubs Vort i 2) 3 (cost i) (deepCost i)):=by
  intro X T Zs Ws htri i hi S G Hs hhist hstate hG hH hbal hdiv f g
  have ht:=htri i hi S G Hs hhist hstate hG hH hbal hdiv
  have hres:=ordinary_triangle_likely_certificate_separate_costs (G.comap f) (F.comap f) (fun v u=>Hs (f v) (g u))
    (markedVortexInnerVertices Vort i) (ordinaryVortexBufferedVertices Vort i 2)
    (markedVortexInnerHubs Vort i) (ordinaryVortexBufferedHubs Vort i 2) (cost i) (deepCost i)
    (by convert ht using 1 <;> congr! 12 <;> exact Subsingleton.elim _ _)
  convert hres using 1 <;> congr! 12 <;> exact Subsingleton.elim _ _
end Oberwolfach
