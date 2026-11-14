module

public import Oberwolfach.OrdinaryRawIntervalSampling

@[expose] public section
/-! The ordinary product experiment depends on its rim probabilities,
not on the particular proof terms used to bound them. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_raw_wheel_law_congr {V U Γ Color:Type}
    [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U]
    (ρ ρ':Sym2 V→ℝ) (hρ:∀e,0≤ρ e) (hρ1:∀e,ρ e≤1)
    (hρ':∀e,0≤ρ' e) (hρ1':∀e,ρ' e≤1) (heq:∀e,ρ e=ρ' e)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)):
    rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS=
      rawWheelLaw ρ' hρ' hρ1' d hd q hq hQ s hs hS :=by
  funext e
  cases e with
  | inl e=>
    dsimp only [rawWheelLaw]
    apply finiteLaw_ext
    intro b
    cases b <;> simp [FiniteLaw.retentionCoin,heq e]
  | inr e=>rfl
end Oberwolfach
