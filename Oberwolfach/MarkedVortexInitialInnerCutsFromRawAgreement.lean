module

public import Oberwolfach.MarkedVortexInitialInnerCutsFromParentRecord
public import Oberwolfach.MarkedInnerRawAgreementRim
public import Oberwolfach.MarkedVortexCorrectedRecordConsequences

@[expose] public section
/-! The old parent record supplies both inner cuts; exact agreement on the
protected pair transfers them to the corrected residual. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_initial_inner_cuts_from_raw_agreement
    (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [Nonempty V] [DecidableEq U]
    (r h k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (σold σglobal:RawMarkedOutcome V U Γ Color) (Hold:Bool→V→U→Prop)
    (βA βrec κold thetaDeep etaBal x eta deltaI hIcut:ℝ)
    (hOld:MarkedVortexCorrectedRecordConsequences r h k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold Hold βA βrec κold thetaDeep etaBal x eta deltaI hIcut)
    (Hordinary:V→U→Prop)
    (hraw:∀e:Sym2 V,e.toFinset⊆Q.extendedVertices 1→σglobal (Sum.inl e)=σold (Sum.inl e))
    (hOrdinary:∀v u,v∈Q.extendedVertices 1→u∈Q.extendedIndices 1→(Hold false v u↔Hordinary v u)):
    let Hnew:Bool→V→U→Prop:=fun b v u=>if b then Hold true v u else Hordinary v u;
    ((∀ mark,BipartiteLargeCut
      (fun x:↥(markedVortexInnerVertices Q 0)=>fun y:↥(markedVortexInnerVertices Q 0)=>
        markedPhysicalRim (G.comap (markedVortexVertexEmbedding Q 0)) (markedVortexPermutation Q π hpres 0) (3*d)
          (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q 0) (markedVortexHubEmbedding Q 0) σglobal (Sum.inl e)) mark x.val y.val) deltaI (2*hIcut)) ∧
    (∀ mark,BipartiteLargeCut (relationMultiplicity (fun x:↥(markedVortexInnerVertices Q 0)=>fun u:↥(markedVortexInnerHubs Q 0)=>
      Hnew mark
        (markedVortexVertexEmbedding Q 0 x.val) (markedVortexHubEmbedding Q 0 u.val))) deltaI (2*hIcut))) := by
  let Residual:=fun mark x y=>markedPhysicalRim G π (3*d) (fun e=>σold (Sum.inl e)) mark x y=1
  have hRnew:∀mark x y,x∈Q.extendedVertices 1→y∈Q.extendedVertices 1→
      (markedPhysicalRim G π (3*d) (fun e=>σglobal (Sum.inl e)) mark x y=1 ↔ Residual mark x y):=by
    exact marked_inner_raw_agreement_rims G π d (Q.extendedVertices 1) (hpres 1) σold σglobal hraw
  exact marked_vortex_initial_inner_cuts_from_parent_record V U Γ Color r h k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold σglobal Hold
      βA βrec κold thetaDeep etaBal x eta deltaI hIcut hOld Hordinary Residual
      (by intro mark x y hx hy; rfl) hRnew hOrdinary
end Oberwolfach
