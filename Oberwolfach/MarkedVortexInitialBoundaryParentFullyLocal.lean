module

public import Oberwolfach.MarkedBoundaryProtectedLocalSlack
public import Oberwolfach.MarkedVortexInitialBalanceParentFullyLocal
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

theorem marked_vortex_initial_boundary_from_parent_fully_local
    (h:ℕ) (x c:ℝ) (hx:0<x) (hc:0≤c) (hcost:2*(h:ℝ)*c≤x/4):
    ∀ζ:ℝ,0≤ζ→
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
    let W:=markedVortexVertexType Q 0
    let Z:=markedVortexHubType Q 0
    let fP:=markedVortexVertexEmbedding Q 0
    let gP:=markedVortexHubEmbedding Q 0
    let ρ:=markedVortexPermutation Q π hpres 0
    let fA:=markedVortexNonDeeperVertexEmbedding Q 0
    let f:=markedVortexNextActiveInNonDeeper Q 0
    let gA:=markedVortexNonDeeperHubToParent Q 0
    let X:=Finset.univ.image f
    let Zinner:=markedVortexInnerNonDeeperHubs Q 0
    let σ:=rawMarkedRestrictPair fP gP σold
    let ω:=rawMarkedRestrictPair fP gP σglobal
    let Hold₀:=fun b v u=>Hold b (fP v) (gP u)
    let H:=fun b v u=>Hglobal b (fP v) (gP u)
    let I:=markedVortexInnerVertices Q 0
    let J:=markedVortexInnerHubs Q 0;
    (∀mark v w,v∈I→w∈I→
      (markedPhysicalRim (G.comap fP) ρ (3*d) (fun e=>σ (Sum.inl e)) mark v w=1 ↔
       markedPhysicalRim (G.comap fP) ρ (3*d) (fun e=>ω (Sum.inl e)) mark v w=1))→
    (∀b v u,v∈I→u∈J→(Hold₀ b v u↔H b v u))→
    (∀v,v∉Q.extendedVertices 1→(FR.degree v:ℝ)≤c*(I.card:ℝ))→
    (∀B:Finset U,∀v,v∉Q.extendedVertices 1→
      (∑u∈B,if ¬(Hold false v u↔Hglobal false v u) then (1:ℝ) else 0)≤c*(I.card:ℝ))→
    (∀v u,Hold₀ true v u↔H true v u)→
    (∀u v,v∈I→H false v u→Hold₀ false v u)→
    (∀u,((I.filter (fun v=>Hold₀ false v u ∧ ¬H false v u)).card:ℝ)≤c*(I.card:ℝ))→
    ∃errR errI:ℝ,0≤errR ∧ 0≤errI ∧ errR≤(x/2)*Fintype.card W ∧ errI≤(x/2)*Fintype.card W ∧
      MarkedRowsWithSpokes (G.comap fP) ρ d h (X.image fA) p kval (fun u=>q (gP u)) (fun u=>s (gP u)) a j errR ω H ∧
      MarkedIndicesWithSpokes ρ d h (Zinner.image gA) (fun u=>q (gP u)) (fun u=>s (gP u)) a j errI ω H := by
  intro ζ hζ V U Γ Color _ _ _ _ _ _ _ r k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold σglobal Hold Hglobal
    βA βrec κ thetaDeep etaBal xold eta deltaI hIcut hxold hOld FR FS hinterval hR hS hFR hFS
    W Z fP gP ρ fA f gA X Zinner σ ω Hold₀ H I J hrim hspoke hFRoutside hrowAmbient hmark hnoNew hloss
  unfold MarkedVortexCorrectedRecordConsequences at hOld
  obtain ⟨_,_,_,_,_,_,_,hboundary⟩:=hOld
  obtain ⟨errR,errI,herrR,herrI,hbR,hbI,hrows,hindices⟩:=hboundary 0 (Nat.zero_le L)
  have hscale:(xold/2)*(Fintype.card W:ℝ)≤(x/4)*Fintype.card W:=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  have hπI:∀v,ρ v∈I↔v∈I:=fun v=>(marked_vortex_permutation_compatibility Q π hpres 0).2.1 v
  have hAI:X.image fA⊆I:=by
    intro v hv
    obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hv
    obtain ⟨z,_,rfl⟩:=Finset.mem_image.mp hu
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    exact z.val.property
  have hBJ:Zinner.image gA⊆J:=by
    rw [marked_vortex_inner_nondeeper_hubs_image]
    exact Finset.sdiff_subset
  have houtside:∀v:W,v∉I→fP v∉Q.extendedVertices 1:=by
    intro v hv hmem
    apply hv
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,hmem⟩
  have hFRlocal:∀v,v∉I→((FR.comap fP).degree v:ℝ)≤c*(I.card:ℝ):=by
    intro v hv
    have hle:((FR.comap fP).degree v:ℝ)≤FR.degree (fP v):=by
      exact_mod_cast graph_comap_injective_degree_le FR fP.toEmbedding v
    exact hle.trans (hFRoutside (fP v) (houtside v hv))
  have hrow:∀v,v∉I→(∑u∈J,if ¬(Hold₀ false v u↔H false v u) then (1:ℝ) else 0)≤c*(I.card:ℝ):=by
    intro v hv
    have hh:=hrowAmbient (J.image gP) (fP v) (houtside v hv)
    rw [Finset.sum_image (fun _ _ _ _ he=>gP.injective he)] at hh
    convert hh using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  have hchanges:=marked_vortex_initial_sample_change_data Q π hpres d σold σglobal Hold Hglobal FR FS ζ hinterval hR hS hFR hFS
  have hdec:(Subtype.instDecidableEq : DecidableEq W)=(fun a b=>Classical.propDecidable (a=b)):=Subsingleton.elim _ _
  try rw [hdec] at hrows hindices ⊢
  exact marked_boundary_protected_local_with_slack (G.comap fP) ρ d h I (X.image fA) J (Zinner.image gA) hAI hBJ hπI
    p kval (fun u=>q (gP u)) (fun u=>s (gP u)) a j errR errI c x hc hx hcost σ ω Hold₀ H hrows hindices
    herrR herrI (hbR.trans hscale) (hbI.trans hscale) (FR.comap fP) hrim hchanges.2.1 hFRlocal hspoke hrow hmark hnoNew hloss
end Oberwolfach
