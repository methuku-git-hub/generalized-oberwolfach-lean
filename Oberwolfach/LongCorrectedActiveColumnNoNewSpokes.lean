module

public import Oberwolfach.LongCorrectedActiveColumnFromLocalSpokes
public import Oberwolfach.FirstVortexActiveLocalSpokeBudget

@[expose] public section
/-! If the completion covers all missing first-vortex targets, there is no
ordinary-spoke gain. The remaining losses fit the first-active cap using
the prescribed-source and assigned-edge budgets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance correctedActiveNoNewFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

theorem long_corrected_active_column_no_new_spokes
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (G:SimpleGraph (Fin n)) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
    (hε:0<ε) (hε1:ε≤1/4) (hm:0<m)
    (π:Equiv.Perm (Fin n)) (d:ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (R:U→Finset (Fin n)) (inner:Finset U) (cap ζ P L:ℝ)
    (hcap:0≤cap) (hζ:0≤ζ) (hloss0:0≤ζ*((Q.extendedVertices 1).card:ℝ)+P+2*L)
    (hζcap:ζ≤cap/128) (hP:P≤cap*(ε*n)/128) (hL:2*L≤cap*(ε*n)/128):
    let A:=Q.extendedVertices 1
    let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J w=>d) Subtype.val
    let H:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t J false false
    let H':=fun b v w=>if b then H true v w else v∈R w\Y w
    let W:=↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1))
    let Z:=markedVortexNonDeeperHubType Q 0
    let f:=markedVortexActiveVertexEmbedding Q 1
    let g:=markedVortexNonDeeperHubToPhysical Q 0
    let HL:=fun b v u=>H b (f v) (g u)
    let HL':=fun b v u=>H' b (f v) (g u)
    let FS:=markedSpokeChangeGraph HL HL';
    (∀w∈inner,∀v∈A,v∈R w\Y w↔H false v w)→
    (∀w∉inner,((A.filter (fun v=>H false v w∧v∉R w\Y w)).card:ℝ)≤ζ*A.card+P+2*L)→
    (∀w v,v∈A→v∈R w\Y w→H false v w)→
    (∀b v u,¬(HL b v u↔HL' b v u)→FS.Adj (Sum.inl v) (Sum.inr u)) ∧
    (∀u:Z,(FS.degree (Sum.inr u):ℝ)≤cap*Fintype.card W) :=by
  intro A Y H H' W Z f g HL HL' FS hexact hloss hNoNew
  let Hold:=fun w=>Finset.univ.filter (fun v=>H false v w)
  have hgain:∀w∉inner,((A∩((R w\Y w)\Hold w)).card:ℝ)≤0:=by
    intro w _
    have hempty:A∩((R w\Y w)\Hold w)=∅:=by
      apply Finset.Subset.antisymm ?_ (Finset.empty_subset _)
      intro v hv
      have hh:=Finset.mem_inter.mp hv
      have hs:=Finset.mem_sdiff.mp hh.2
      have hhold:v∈Hold w:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,hNoNew w v hh.1 hs.1⟩
      exact False.elim (hs.2 hhold)
    rw [hempty]
    simp
  have hzero:0≤cap*(ε*n)/128:=by positivity
  have hP':P≤cap*(ε*Fintype.card (Fin n))/128:=by simpa only [Fintype.card_fin] using hP
  have hL':2*L≤cap*(ε*Fintype.card (Fin n))/128:=by simpa only [Fintype.card_fin] using hL
  have hzero':0≤cap*(ε*Fintype.card (Fin n))/128:=by simpa only [Fintype.card_fin] using hzero
  have hbudget:=first_vortex_active_local_spoke_budget G D m β ε Q hε hε1 hm cap 0 ζ P L 0 0
    hcap (by positivity) hζcap hP' hL' hzero' hzero'
  have hterm:0≤ζ*(A.card:ℝ):=mul_nonneg hζ (Nat.cast_nonneg _)
  have hscale:(ζ*(A.card:ℝ)+P+2*L)+0≤cap*Fintype.card W:=by
    dsimp only [A,W] at *
    nlinarith [hbudget]
  exact long_corrected_active_column_from_local_spokes G D m β ε Q π d raw t J R inner
    (ζ*(A.card:ℝ)+P+2*L) 0 cap hloss0 (by norm_num) hexact hloss hgain hscale
end Oberwolfach
