module

public import Oberwolfach.MarkedVortexInitialInnerCutsTransfer
public import Oberwolfach.MarkedInnerCutsOfExactAgreement
public import Oberwolfach.MarkedPhysicalCutTransfer
public import Oberwolfach.MarkedFixedVortexGeometry

@[expose] public section
/-! Exact first-inner agreement preserves both initial-parent cut fields. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_initial_inner_cuts_from_residual
    (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
    (π:Equiv.Perm V) (hπ:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
    (d:ℕ) (σglobal τglobal:RawMarkedOutcome V U Γ Color)
    (Hglobal:Bool→V→U→Prop) (Hordinary:V→U→Prop) (Residual:Bool→V→V→Prop)
    (hOld:∀mark x y,x∈Q.extendedVertices 1→y∈Q.extendedVertices 1→
      (markedPhysicalRim G π (3*d) (fun e=>σglobal (Sum.inl e)) mark x y=1 ↔ Residual mark x y))
    (hNew:∀mark x y,x∈Q.extendedVertices 1→y∈Q.extendedVertices 1→
      (markedPhysicalRim G π (3*d) (fun e=>τglobal (Sum.inl e)) mark x y=1 ↔ Residual mark x y))
    (hOrdinary:∀x u,x∈Q.extendedVertices 1→u∈Q.extendedIndices 1→(Hglobal false x u↔Hordinary x u))
    (δ c:ℝ):
    let Hglobal':=fun (b:Bool) (v:V) (u:U)=>if b then Hglobal true v u else Hordinary v u
    let W:=markedVortexVertexType Q 0
    let Z:=markedVortexHubType Q 0
    let f:=markedVortexVertexEmbedding Q 0
    let g:=markedVortexHubEmbedding Q 0
    let ρ:=markedVortexPermutation Q π hπ 0
    let P:=G.comap f
    let σ:=rawMarkedRestrictPair f g σglobal
    let τ:=rawMarkedRestrictPair f g τglobal
    let H:=fun b v u=>Hglobal b (f v) (g u)
    let H':=fun b v u=>Hglobal' b (f v) (g u)
    let I:=markedVortexInnerVertices Q 0
    let J:=markedVortexInnerHubs Q 0;
    (∀mark,BipartiteLargeCut (fun x:I=>fun y:I=>markedPhysicalRim P ρ (3*d) (fun e=>σ (Sum.inl e)) mark x.val y.val) δ c)→
    (∀mark,BipartiteLargeCut (relationMultiplicity (fun x:I=>fun u:J=>H mark x.val u.val)) δ c)→
    (∀mark,BipartiteLargeCut (fun x:I=>fun y:I=>markedPhysicalRim P ρ (3*d) (fun e=>τ (Sum.inl e)) mark x.val y.val) δ c) ∧
    (∀mark,BipartiteLargeCut (relationMultiplicity (fun x:I=>fun u:J=>H' mark x.val u.val)) δ c) := by
  intro Hglobal' W Z f g ρ P σ τ H H' I J hrim hspoke
  have hR:∀mark x y,x∈Q.extendedVertices 1→y∈Q.extendedVertices 1→
      (markedPhysicalRim G π (3*d) (fun e=>σglobal (Sum.inl e)) mark x y=1 ↔
       markedPhysicalRim G π (3*d) (fun e=>τglobal (Sum.inl e)) mark x y=1):=by
    intro mark x y hx hy
    exact (hOld mark x y hx hy).trans (hNew mark x y hx hy).symm
  have hS:∀b x u,x∈Q.extendedVertices 1→u∈Q.extendedIndices 1→(Hglobal b x u↔Hglobal' b x u):=by
    intro b x u hx hu
    cases b with
    | false => simpa only [Hglobal',Bool.false_eq_true,ite_false] using hOrdinary x u hx hu
    | true => simp only [Hglobal',ite_true,iff_self]
  exact marked_vortex_initial_inner_cuts_transfer V U Γ Color G D m β ε Q π hπ d σglobal τglobal Hglobal Hglobal' hR hS δ c hrim hspoke
end Oberwolfach
