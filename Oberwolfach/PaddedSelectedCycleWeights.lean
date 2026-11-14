module

public import Oberwolfach.FixedLengthPadding
public import Oberwolfach.PreparationWeightsFromAllowedThreshold

@[expose] public section
/-! Extend only the already constructed cycle weights; unselected lengths
receive the zero function and selected weights retain their exact edge sums. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem padded_selected_cycle_weights {V:Type} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (K:ℕ) (n:Fin K→ℕ) (B:Fin K→ℝ) (hB:∀ i,0≤B i)
    (S:Finset (Fin K))
    (w:∀ i:↥S,OrdinaryCycle G (n i.val+2)→ℝ)
    (hw:∀ i C,0≤w i C ∧ w i C≤B i.val/(Fintype.card V:ℝ)^(n i.val))
    (he:∀ i x y,(∑ C,if C.val.val.Adj x y then w i C else 0)=if G.Adj x y then 1 else 0):
    ∃ wfull:∀ i:Fin K,OrdinaryCycle G (n i+2)→ℝ,
      (∀ i C,0≤wfull i C ∧ wfull i C≤B i/(Fintype.card V:ℝ)^(n i)) ∧
      (∀ i:↥S,∀ C,wfull i.val C=w i C) ∧
      (∀ i:↥S,∀ x y,(∑ C,if C.val.val.Adj x y then wfull i.val C else 0)=if G.Adj x y then 1 else 0) ∧
      (∀ i∉S,∀ C,wfull i C=0):=by
  let X:=fun i:Fin K=>OrdinaryCycle G (n i+2)
  let wfull:=padIndexedFunctions S X w
  refine ⟨wfull,?_,?_,?_,?_⟩
  · apply pad_indexed_functions_bounds S X w (fun i=>B i/(Fintype.card V:ℝ)^(n i))
    · intro i;have hi:=hB i;positivity
    · exact hw
  · intro i C
    exact pad_indexed_functions_on S X w i C
  · intro i x y
    have hwEq:∀ C,wfull i.val C=w i C:=pad_indexed_functions_on S X w i
    simp_rw [hwEq]
    exact he i x y
  · intro i hi C
    exact pad_indexed_functions_off S X w i hi C
end Oberwolfach
