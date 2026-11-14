module

public import Oberwolfach.RawOrdinaryIndexEvent

@[expose] public section
/-! An index event yields the absorber's common-hub lower bounds when the
explicit density margin holds at each order under consideration. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]
theorem ordinary_index_event_absorber_hub_bound
    (F:SimpleGraph V) (π:Equiv.Perm V) (d h:ℕ) (pH:ℝ)
    (j:Color) (t β:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (hevent:RawOrdinaryIndices F π d h pH j t σ)
    (hmargin:∀ k:ℕ,k≤h → β*Fintype.card V+t≤pH^k*Fintype.card U):
    ∀ T:Finset V,T.card≤h→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
      β*Fintype.card V≤((common Finset.univ T (fun v=>Finset.univ.filter (rawWheelSpokes π d σ j v))).card:ℝ) := by
  intro T hT hind
  have hcount:=hevent T hT hind
  have hm:=hmargin T.card hT
  have hl: -t<((common Finset.univ T (fun v=>Finset.univ.filter (rawWheelSpokes π d σ j v))).card:ℝ)-pH^T.card*Fintype.card U := (abs_lt.mp hcount).1
  linarith
end Oberwolfach
