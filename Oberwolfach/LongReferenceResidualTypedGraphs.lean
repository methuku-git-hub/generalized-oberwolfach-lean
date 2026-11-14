module

public import Oberwolfach.LongDualReferenceAgreementAwayChanges

@[expose] public section
/-! Physical graphs of each selected reference type and each corrected
residual type, on the same ambient vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
local instance referenceResidualTypedDecEq : DecidableEq V := Classical.decEq V
local instance referenceResidualTypedArc (P:V×V→Prop):DecidableEq {e:V×V // P e}:=Classical.decEq _

def longReferenceTypedGraph
    (G:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) (mark:Bool):SimpleGraph V where
  Adj x y:=(longSelectedPhysicalGraph G π d ω).Adj x y ∧
    (if mark then
      markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) true x (π.symm y)=1 ∨
      markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) true y (π.symm x)=1
    else
      markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) false x y=1 ∨
      markedPhysicalRim G π (3*d) (fun e=>markedExpandedPhysicalCollapse (ω (Sum.inl e))) false y x=1)
  symm:=⟨by
    intro x y h
    refine ⟨h.1.symm,?_⟩
    cases mark <;> simp only [Bool.false_eq_true,↓reduceIte] at h ⊢ <;> exact h.2.symm⟩
  loopless:=⟨by intro x h;exact h.1.ne rfl⟩

def longResidualTypedGraph
    (S Small:SimpleGraph V) (M:V→V→ℕ)
    (T:Finset {e:V×V // longEligibleResidualArc M Small ⊥ e}) (mark:Bool):SimpleGraph V where
  Adj x y:=(S\Small).Adj x y ∧
    ∃e:{a:V×V // longEligibleResidualArc M Small ⊥ a},
      (e.val=(x,y)∨e.val=(y,x)) ∧ (if mark then e∈T else e∉T)
  symm:=⟨by
    intro x y h
    obtain ⟨hS,e,he,ht⟩:=h
    exact ⟨hS.symm,e,he.symm,ht⟩⟩
  loopless:=⟨by intro x h;exact h.1.ne rfl⟩

theorem long_reference_typed_subgraph
    (G:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) (mark:Bool):
    longReferenceTypedGraph G π d ω mark≤longSelectedPhysicalGraph G π d ω:=by
  intro x y h
  exact h.1

theorem long_residual_typed_subgraph
    (S Small:SimpleGraph V) (M:V→V→ℕ)
    (T:Finset {e:V×V // longEligibleResidualArc M Small ⊥ e}) (mark:Bool):
    longResidualTypedGraph S Small M T mark≤S\Small:=by
  intro x y h
  exact h.1
end Oberwolfach
