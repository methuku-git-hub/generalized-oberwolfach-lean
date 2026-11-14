module

public import Oberwolfach.OrdinaryShiftedMarkedResourceState
public import Oberwolfach.MarkedOrdinaryResourceLoads

@[expose] public section
/-! Unmarked wheel loads use the same ordinary physical state when embedded
in the shifted-wheel resource universe. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color C:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype C]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_shifted_state_on_unmarked_resource
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (g:Γ) (j:Color)
    (σ:RawMarkedOutcome V U Γ Color) (root:(V×V)⊕(V×U)):
    typedMarkedResourceState (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j)
      (ordinaryMarkedResourceEmbedding root)=orderedOrdinaryResourceState P π d g j σ root :=by
  cases root with
  | inl xy=>
    simp only [orderedOrdinaryResourceState,ordinaryMarkedResourceEmbedding,Function.Embedding.coeFn_mk,
      orderedOrdinaryResourceEmbedding,typedMarkedResourceState,Sum.elim_inl,ordinaryShiftedPairRims,
      rawMarkedPairRims,markedPhysicalRim_eq_one_iff,Bool.false_eq_true,ite_false]
    have he:s(xy.1,if false=true then π xy.2 else xy.2)=s(xy.1,xy.2):=by simp
    have hh:=congrArg (fun e:Sym2 V=>σ (Sum.inl e)) he
    rw [hh]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
  | inr a=>rfl

theorem ordinary_shifted_unmarked_load_bridge
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (g:Γ) (j:Color)
    (σ:RawMarkedOutcome V U Γ Color) (R:C→Finset ((V×V)⊕(V×U))) (w:C→ℝ)
    (root:(V×V)⊕(V×U)):
    resourcePatternLoad (fun c=>(R c).map ordinaryMarkedResourceEmbedding) w (fun _ _=>true)
      (ordinaryMarkedResourceEmbedding root)
      (typedMarkedResourceState (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j))=
    resourcePatternLoad R w (fun _ _=>true) root (orderedOrdinaryResourceState P π d g j σ) :=by
  rw [ordinary_load_in_marked_universe]
  congr 1
  funext a
  exact ordinary_shifted_state_on_unmarked_resource P π d g j σ a
end Oberwolfach
