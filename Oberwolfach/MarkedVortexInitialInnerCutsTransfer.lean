module

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

theorem marked_vortex_initial_inner_cuts_transfer
    (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
    (π:Equiv.Perm V) (hπ:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
    (d:ℕ) (σglobal τglobal:RawMarkedOutcome V U Γ Color) (Hglobal Hglobal':Bool→V→U→Prop)
    (hR:∀mark x y,x∈Q.extendedVertices 1→y∈Q.extendedVertices 1→
      (markedPhysicalRim G π (3*d) (fun e=>σglobal (Sum.inl e)) mark x y=1 ↔
       markedPhysicalRim G π (3*d) (fun e=>τglobal (Sum.inl e)) mark x y=1))
    (hS:∀b x u,x∈Q.extendedVertices 1→u∈Q.extendedIndices 1→(Hglobal b x u↔Hglobal' b x u))
    (δ c:ℝ):
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
  intro W Z f g ρ P σ τ H H' I J hrim hspoke
  have hcomm:∀v,f (ρ v)=π (f v):=(marked_vortex_permutation_compatibility Q π hπ 0).1
  have hf:∀v,v∈I → f v∈Q.extendedVertices 1:=by
    intro v hv
    change v.val∈Q.extendedVertices 1
    simpa only [I,markedVortexInnerVertices,Finset.mem_filter,Finset.mem_univ,true_and,zero_add] using hv
  have hg:∀u,u∈J → g u∈Q.extendedIndices 1:=by
    intro u hu
    change u.val∈Q.extendedIndices 1
    simpa only [J,markedVortexInnerHubs,Finset.mem_filter,Finset.mem_univ,true_and,zero_add] using hu
  have hlocalR:∀mark x y,x∈I→y∈I→
      (markedPhysicalRim P ρ (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
       markedPhysicalRim P ρ (3*d) (fun e=>τ (Sum.inl e)) mark x y=1):=by
    intro mark x y hx hy
    rw [markedPhysicalRim_restrictPair_eq f g π ρ hcomm G d σglobal mark x y,
      markedPhysicalRim_restrictPair_eq f g π ρ hcomm G d τglobal mark x y]
    exact hR mark (f x) (f y) (hf x hx) (hf y hy)
  have hdec:(Subtype.instDecidableEq : DecidableEq W)=(fun a b=>Classical.propDecidable (a=b)):=Subsingleton.elim _ _
  try rw [hdec] at hrim
  try rw [hdec] at hspoke
  try rw [hdec]
  exact marked_inner_cuts_of_exact_agreement P ρ d σ τ H H' I J hlocalR
    (fun b x u hx hu=>hS b (f x) (g u) (hf x hx) (hg u hu)) δ c hrim hspoke
end Oberwolfach
