module

public import Oberwolfach.OrdinaryVortexInitialDeepSampleBalance
public import Oberwolfach.OrdinaryPhysicalEditToTypedChanges

@[expose] public section
/-! At the first parent, two-step tests and the actual physical edit bound
supply the deeper balance before any level deletion has been made. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_initial_zero_two_step_deep_balance
    (P F:SimpleGraph V) (D m:ℕ) (β ε pR pH εR εH Ledit:ℝ)
    (Q:Vortex U P D β ε m) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (hn:0<Fintype.card V) (hreg:P.IsRegularOfDegree D) (hρ:0< initialIndexDensity U D)
    (hβ:0≤β) (hpH:0≤pH) (hεR:0≤εR) (hεH:0≤εH) (hL:0≤Ledit)
    (hpR:pR=initialIndexDensity U D*pH)
    (hgood:OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P F D m β ε Q π hπ pR pH s j σ):
    let f:=markedVortexVertexEmbedding Q 0;let g:=markedVortexHubEmbedding Q 0;
    let ρ:=markedVortexPermutation Q π hπ 0;let raw:=ordinaryRawRestrictPair f g σ;
    let T:=ordinaryVortexBufferedVertices Q 0 2;let W:=ordinaryVortexBufferedHubs Q 0 2;
    ∀(G:SimpleGraph (markedVortexVertexType Q 0)) (H:markedVortexVertexType Q 0→markedVortexHubType Q 0→Prop),
    (∀z:markedVortexVertexType Q 0⊕markedVortexHubType Q 0,
      ((changed ((ordinaryPhysicalGraph (rawWheelGraph (P.comap f) raw) (rawWheelSpokes ρ d raw j)).neighborFinset z)
        ((ordinaryPhysicalGraph G H).neighborFinset z)).card:ℝ)≤Ledit)→
    ∀v,|((G.neighborFinset v∩T).card:ℝ)-2*(W.filter (H v)).card|≤
      (initialIndexDensity U D*pH)*β*T.card+εR*T.card+2*(εH*W.card)+3*Ledit:=by
  intro f g ρ raw T W G H hphysical v
  by_cases htarget:2≤Q.length
  · have tests:=hgood 0 (by omega)
    have hrows:RawOrdinaryRows (P.comap f) ρ d 2 T pR (fun u=>s (g u)) j (εR*T.card) raw:=by
      intro S J hS hJ
      exact tests.1 S J (by omega) (by omega)
    have hedits:=ordinary_physical_edit_to_typed_changes (rawWheelGraph (P.comap f) raw) G (rawWheelSpokes ρ d raw j) H Ledit hphysical
    have hrim:∀x,((changed (G.neighborFinset x) ((rawWheelGraph (P.comap f) raw).neighborFinset x)).card:ℝ)≤Ledit:=by
      intro x
      simpa [changed,Finset.union_comm] using hedits.1 x
    have hspoke:∀x,((changed (Finset.univ.filter (H x)) (Finset.univ.filter (rawWheelSpokes ρ d raw j x))).card:ℝ)≤Ledit:=by
      intro x
      simpa [changed,Finset.union_comm] using hedits.2.1 x
    have hh:=ordinary_vortex_deep_sample_balance P F D m β ε pR pH εR εH Ledit Q π hπ d s j σ
      hn hreg hρ hβ hpH hεR hεH hL hpR 0 G H hrows tests.2
      (by intro x;convert hrim x using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
      (by intro x;convert hspoke x using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) v
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · have hV:Q.extendedVertices (0+2)=∅:=Q.extendedVertices_empty (by omega)
    have hU:Q.extendedIndices (0+2)=∅:=Q.extendedIndices_empty (by omega)
    have hT:T=∅:=by simp [T,ordinaryVortexBufferedVertices,hV]
    have hW:W=∅:=by simp [W,ordinaryVortexBufferedHubs,hU]
    simp only [hT,hW,Finset.inter_empty,Finset.filter_empty,Finset.card_empty,Nat.cast_zero,mul_zero,sub_zero,abs_zero,zero_add]
    positivity
end Oberwolfach
