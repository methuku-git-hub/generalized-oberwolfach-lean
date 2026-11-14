module

public import Oberwolfach.MarkedVortexInitialActiveColumnFromHubLocal
public import Oberwolfach.LongResidualSpokeLocalLoss

@[expose] public section
/-! Feed the actual residual ordinary-spoke sets into the first-active
change graph, keeping retained marked spokes unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance correctedActiveColumnLocalFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

theorem long_corrected_active_column_from_local_spokes
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (G:SimpleGraph (Fin n)) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
    (π:Equiv.Perm (Fin n)) (d:ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (R:U→Finset (Fin n)) (inner:Finset U) (loss gain ζ:ℝ) (hloss:0≤loss) (hgain:0≤gain):
    let A:=Q.extendedVertices 1
    let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J w=>d) Subtype.val
    let H:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t J false false
    let Hold:=fun w=>Finset.univ.filter (fun v=>H false v w)
    let H':=fun b v w=>if b then H true v w else v∈R w\Y w
    let W:=↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1))
    let Z:=markedVortexNonDeeperHubType Q 0
    let f:=markedVortexActiveVertexEmbedding Q 1
    let g:=markedVortexNonDeeperHubToPhysical Q 0
    let HL:=fun b v u=>H b (f v) (g u)
    let HL':=fun b v u=>H' b (f v) (g u)
    let FS:=markedSpokeChangeGraph HL HL';
    (∀w∈inner,∀v∈A,v∈R w\Y w↔H false v w)→
    (∀w∉inner,((A.filter (fun v=>H false v w∧v∉R w\Y w)).card:ℝ)≤loss)→
    (∀w∉inner,((A∩((R w\Y w)\Hold w)).card:ℝ)≤gain)→
    loss+gain≤ζ*Fintype.card W→
    (∀b v u,¬(HL b v u↔HL' b v u)→FS.Adj (Sum.inl v) (Sum.inr u)) ∧
    (∀u:Z,(FS.degree (Sum.inr u):ℝ)≤ζ*Fintype.card W) :=by
  intro A Y H Hold H' W Z f g HL HL' FS hexact hloss' hgain' hscale
  have hmark:∀v w,H true v w↔H' true v w:=by intro v w; simp [H']
  have hEq:∀w∈inner,∀v∈A,H false v w↔H' false v w:=by
    intro w hw v hv
    simpa only [H',Bool.false_eq_true,if_false] using (hexact w hw v hv).symm
  have hLoss:∀w∉inner,((A.filter (fun v=>H false v w∧¬H' false v w)).card:ℝ)≤loss:=by
    intro w hw
    simpa only [H',Bool.false_eq_true,if_false] using hloss' w hw
  have hGain:∀w∉inner,((A.filter (fun v=>H' false v w∧¬H false v w)).card:ℝ)≤gain:=by
    intro w hw
    have heq:A.filter (fun v=>H' false v w∧¬H false v w)=A∩((R w\Y w)\Hold w):=by
      ext v
      simp only [Finset.mem_filter,Finset.mem_inter,Finset.mem_sdiff,Hold,Finset.mem_univ,true_and,H',Bool.false_eq_true,if_false]
    rw [heq]
    exact hgain' w hw
  apply marked_vortex_initial_active_column_from_hub_local G D m β ε Q H H' inner hmark loss gain ζ hloss hgain hEq ?_ ?_ hscale
  · intro w hw
    convert hLoss w hw using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
  · intro w hw
    convert hGain w hw using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
end Oberwolfach
