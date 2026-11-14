module

public import Oberwolfach.ClassOrientationCorrectionGraph
public import Oberwolfach.LongPreparationPhysicalStates
public import Oberwolfach.ExpandedSampleOrientation

@[expose] public section
/-! The deletion needed for matching is measured only on sampled class edges;
selected and approximate arcs both lie in that sampled class. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_arc_sampled_class
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) (x y:V)
    (h:rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y):
    (longPhysicalStateGraph P σ {0,1,2,3,4}).Adj x y ∧
      sampledOrientation (longPhysicalStateGraph P σ {0,1,2,3,4}) (fun e=>(σ (Sum.inl e)).2) x y=1:=by
  have hh:=(markedPhysicalRim_eq_one_iff P π (3*d) _ false x y).mp h
  have hstate:(σ (Sum.inl s(x,y))).1=0:=by
    have hs:=hh.2.2
    change markedExpandedPhysicalCollapse (σ (Sum.inl s(x,y)))=some (false,orientationBit x y) at hs
    unfold markedExpandedPhysicalCollapse at hs
    split_ifs at hs <;> simp_all
  have hclass:(longPhysicalStateGraph P σ {0,1,2,3,4}).Adj x y:=⟨hh.2.1,by simp [hstate]⟩
  have hsample:=expanded_selected_relation_uses_sampled_orientation P π d (fun e=>σ (Sum.inl e)) x y h
  have hp:P.Adj x y:=by simpa using hh.2.1
  refine ⟨hclass,?_⟩
  simpa [sampledOrientation,hclass,hp] using hsample

theorem approximate_arc_sampled_class
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) (x y:V)
    (h:rawMixedPhysicalArc P π d (fun e=>rawExpandedApproximateCollapse e (σ e)) x y):
    (longPhysicalStateGraph P σ {0,1,2,3,4}).Adj x y ∧
      sampledOrientation (longPhysicalStateGraph P σ {0,1,2,3,4}) (fun e=>(σ (Sum.inl e)).2) x y=1:=by
  have hsample:=expanded_approximate_arc_uses_sampled_orientation P π d σ x y h
  have hP:P.Adj x y:=by
    by_contra hn
    simp [sampledOrientation,hn] at hsample
  have hstate:(σ (Sum.inl s(x,y))).1=2 ∨ (σ (Sum.inl s(x,y))).1=3:=by
    rcases h with h|h
    · have hh:=(markedPhysicalRim_eq_one_iff P π (3*d) _ false x y).mp h
      have hs:=hh.2.2
      change markedExpandedApproximateCollapse (σ (Sum.inl s(x,y)))=some (false,orientationBit x y) at hs
      unfold markedExpandedApproximateCollapse at hs
      split_ifs at hs <;> simp_all
    · have hh:=(markedPhysicalRim_eq_one_iff P π (3*d) _ true x (π.symm y)).mp h
      have hs:=hh.2.2
      simp only [rawExpandedApproximateCollapse] at hs
      dsimp at hs
      simp only [Equiv.apply_symm_apply] at hs
      unfold markedExpandedApproximateCollapse at hs
      split_ifs at hs with htwo hthree
      · simp at hs
      · right
        have heq:(σ (Sum.inl s(x,π (π.symm y)))).1=(σ (Sum.inl s(x,y))).1:=
          congrArg (fun e:Sym2 V=>(σ (Sum.inl e)).1) (by simp)
        exact heq.symm.trans hthree
  have hclass:(longPhysicalStateGraph P σ {0,1,2,3,4}).Adj x y:=⟨hP,by rcases hstate with h|h <;> simp [h]⟩
  refine ⟨hclass,?_⟩
  simpa [sampledOrientation,hclass,hP] using hsample

theorem sampled_class_arc_follows_corrected_orientation
    {V:Type} [Fintype V] [LinearOrder V] (S₀ Del:SimpleGraph V) (bits:Sym2 V→Bool)
    (M:V→V→ℕ) (hcorrect:orientationDisagreementGraph S₀ bits M≤Del):
    ∀x y,S₀.Adj x y→sampledOrientation S₀ bits x y=1→¬Del.Adj x y→M x y=1:=by
  intro x y hS hbit hDel
  by_contra hn
  exact hDel (hcorrect ⟨hS,Or.inl (by simpa [hbit] using hn)⟩)
end Oberwolfach
