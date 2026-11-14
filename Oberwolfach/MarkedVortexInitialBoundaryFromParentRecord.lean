module

public import Oberwolfach.MarkedVortexInitialBoundaryRowsWithSlack
public import Oberwolfach.MarkedVortexCorrectedRecordConsequences

@[expose] public section
/-! Transfer the selected parent's actual boundary rows to the corrected
sample, using the stricter original boundary allowance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_initial_boundary_from_parent_record
    (h:ℕ) (x:ℝ) (hx:0<x):
    ∃cap:ℝ,0<cap ∧ ∀ζ:ℝ,0≤ζ→ζ≤cap→
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    ∀ (r k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (σold σglobal:RawMarkedOutcome V U Γ Color) (Hold Hglobal:Bool→V→U→Prop)
    (βA βrec κ thetaDeep etaBal xold eta deltaI hIcut:ℝ) (hxold:xold≤x/2)
    (hOld:MarkedVortexCorrectedRecordConsequences r h k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold Hold βA βrec κ thetaDeep etaBal xold eta deltaI hIcut)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hinterval:∀e,σold (Sum.inr e)=σglobal (Sum.inr e))
    (hR:∀e,¬(rawMarkedPairRims G π d σold e↔rawMarkedPairRims G π d σglobal e)→markedPairPhysical π e∈FR.edgeFinset)
    (hS:∀b v u,¬(Hold b v u↔Hglobal b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hFR:∀v,(FR.degree v:ℝ)≤ζ*Fintype.card V) (hFS:∀z,(FS.degree z:ℝ)≤ζ*Fintype.card V),
    (let W:=markedVortexVertexType Q 0
      let Z:=markedVortexHubType Q 0
      let fP:=markedVortexVertexEmbedding Q 0
      let gP:=markedVortexHubEmbedding Q 0
      let ρ:=markedVortexPermutation Q π hpres 0
      let fA:=markedVortexNonDeeperVertexEmbedding Q 0
      let f:=markedVortexNextActiveInNonDeeper Q 0
      let gA:=markedVortexNonDeeperHubToParent Q 0
      let X:=Finset.univ.image f
      let Zinner:=markedVortexInnerNonDeeperHubs Q 0
      let ω:=rawMarkedRestrictPair fP gP σglobal
      let H:=fun b x u=>Hglobal b (fP x) (gP u);
      ∃ errR errI:ℝ,0≤errR ∧ 0≤errI ∧ errR≤(x/2)*Fintype.card W ∧ errI≤(x/2)*Fintype.card W ∧
        MarkedRowsWithSpokes (G.comap fP) ρ d h (X.image fA) p kval (fun u=>q (gP u)) (fun u=>s (gP u)) a j errR ω H ∧
        MarkedIndicesWithSpokes ρ d h (Zinner.image gA) (fun u=>q (gP u)) (fun u=>s (gP u)) a j errI ω H) := by
  obtain ⟨cap,hcap,htransfer⟩:=marked_vortex_initial_boundary_rows_with_slack h x hx
  refine ⟨cap,hcap,?_⟩
  intro ζ hζ hζcap V U Γ Color _ _ _ _ _ _ _ r k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold σglobal Hold Hglobal
    βA βrec κ thetaDeep etaBal xold eta deltaI hIcut hxold hOld FR FS hinterval hR hS hFR hFS
  unfold MarkedVortexCorrectedRecordConsequences at hOld
  obtain ⟨_,_,_,_,_,_,_,hboundary⟩:=hOld
  obtain ⟨errR,errI,herrR,herrI,hbR,hbI,hrows,hindices⟩:=hboundary 0 (Nat.zero_le L)
  have hscale:(xold/2)*(Fintype.card (markedVortexVertexType Q 0):ℝ)≤(x/4)*Fintype.card (markedVortexVertexType Q 0):=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  exact htransfer ζ hζ hζcap V U Γ Color G D m β ε Q π hpres d σold σglobal Hold Hglobal FR FS hinterval hR hS hFR hFS
    _ _ p kval errR errI _ _ a j herrR herrI (hbR.trans hscale) (hbI.trans hscale) hrows hindices
end Oberwolfach
