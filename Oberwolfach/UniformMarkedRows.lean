module

public import Oberwolfach.MarkedRowCommonEvent
public import Oberwolfach.ExponentialConfigurationMargins

@[expose] public section

/-! Exponential failure for all bounded-size marked row patterns at the
original inner order. The rate and coefficient are independent of the host,
fixed domains and actual feasible spoke marginals. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def markedRowsCoefficient (h : ℕ) (K : ℝ) : ℝ := (4*K+1)^(2*h)*(2*K+1)^h

def markedRowsExponent (h d : ℕ) (ε : ℝ) : ℝ :=
  2*ε^2/((8*(d:ℝ)+6)^2*(2*(2*(h:ℝ)+1)))

theorem markedRowsExponent_pos (h d : ℕ) (ε : ℝ) (hε : 0<ε) :
    0<markedRowsExponent h d ε := by unfold markedRowsExponent;positivity

theorem rawMarkedRows_exponential_event
    {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (A : Finset V) (hA : A.Nonempty) (K ε : ℝ) (hK : 1≤K) (hε : 0<ε)
    (hV : (Fintype.card V:ℝ)≤K*A.card) (hU : (Fintype.card U:ℝ)≤K*A.card)
    (h : ℕ) (g : Γ) (j : Color) :
    1-2*markedRowsCoefficient h K*(A.card:ℝ)^(3*h)*Real.exp (-markedRowsExponent h d ε*A.card)≤
      (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).probability
        (RawMarkedRows P π d h A p k q s g j (ε*A.card)) := by
  have ha : (0:ℝ)<A.card := by exact_mod_cast hA.card_pos
  have ha1 : (1:ℝ)≤A.card := by exact_mod_cast hA.card_pos
  have hK0 : 0<K := by linarith
  have hV' : 4*(Fintype.card V:ℝ)+1≤(4*K+1)*A.card := by nlinarith only [hV,ha1]
  have hU' : 2*(Fintype.card U:ℝ)+1≤(2*K+1)*A.card := by nlinarith only [hU,ha1]
  have hcard : (4*(Fintype.card V:ℝ)+1)^(2*h)*(2*(Fintype.card U:ℝ)+1)^h≤
      markedRowsCoefficient h K*(A.card:ℝ)^(3*h) := by
    calc
      _≤((4*K+1)*A.card)^(2*h)*((2*K+1)*A.card)^h := by gcongr
      _=_ := by
        dsimp [markedRowsCoefficient]
        simp only [mul_pow]
        rw [show 3*h=2*h+h by omega,pow_add]
        ring
  have herr := linear_deviation_failure_exponential (markedRowsCoefficient h K)
    ((8*(d:ℝ)+6)^2*(2*(2*(h:ℝ)+1))) ε (by positivity) hε (3*h) A.card hA.card_pos
    ((4*(Fintype.card V:ℝ)+1)^(2*h)*(2*(Fintype.card U:ℝ)+1)^h)
    ((8*(d:ℝ)+6)^2*(2*(2*(h:ℝ)+1)*A.card)) (by positivity) hcard (by positivity)
    (by exact le_of_eq (by ring))
  have hh := rawMarkedRows_common_event P π d hd p k hp hk hsum q hq hQ s hs hS hnoshort
    A hA h g j (ε*A.card) (by positivity)
  exact (sub_le_sub_left herr 1).trans hh

end Oberwolfach
