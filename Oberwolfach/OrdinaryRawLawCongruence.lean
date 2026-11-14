module

public import Oberwolfach.OrdinaryRawIntervalSampling

@[expose] public section
/-! A change of notation for the parameters does not change the law. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]
theorem raw_wheel_law_congr (d:ℕ) (hd:2≤d)
    (ρ ρ':Sym2 V→ℝ) (hρ:∀e,0≤ρ e) (hρ1:∀e,ρ e≤1)
    (hρ':∀e,0≤ρ' e) (hρ1':∀e,ρ' e≤1)
    (q q':U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (hq':∀u g,0≤q' u g) (hQ':∀u,∑g,q' u g≤1/8)
    (s s':U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hs':∀u j,0≤s' u j)
    (hS':∀u,∑j,s' u j≤ intervalUncoveredProbability d (∑g,q' u g))
    (hρeq:ρ=ρ') (hqeq:q=q') (hseq:s=s'):
    rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS =
    rawWheelLaw ρ' hρ' hρ1' d hd q' hq' hQ' s' hs' hS' :=by
  subst ρ'
  subst q'
  subst s'
  rfl
end Oberwolfach
