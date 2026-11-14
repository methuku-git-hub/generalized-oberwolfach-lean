module

public import Oberwolfach.RawOrdinaryRowEvent
public import Oberwolfach.ExponentialConfigurationMargins

@[expose] public section
/-! Row tests have an exponential local-domain failure bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinaryRowsCoefficient (h:ℕ) (K:ℝ):ℝ:=(K+1)^(2*h)
def ordinaryRowsExponent (h d:ℕ) (ε:ℝ):ℝ:=
  2*ε^2/((4*(d:ℝ)+3)^2*(2*(2*(h:ℝ)+1)))

theorem ordinary_rows_exponent_pos (h d:ℕ) (ε:ℝ) (hε:0<ε):0<ordinaryRowsExponent h d ε:=by
  unfold ordinaryRowsExponent
  positivity

theorem raw_ordinary_rows_exponential_event
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (p:ℝ) (hp:0≤p) (hp1:p≤1)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x k,0<k→k<2*d+1→(π^k) x≠x)
    (A:Finset V) (hA:A.Nonempty) (K ε:ℝ) (hK:1≤K) (hε:0<ε)
    (hV:(Fintype.card V:ℝ)≤K*A.card) (hU:(Fintype.card U:ℝ)≤K*A.card)
    (h:ℕ) (j:Color):
    1-2*ordinaryRowsCoefficient h K*(A.card:ℝ)^(2*h)*Real.exp (-ordinaryRowsExponent h d ε*A.card)≤
      (FiniteLaw.pi (rawWheelLaw (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS)).probability
        (RawOrdinaryRows P π d h A p s j (ε*A.card)):=by
  have ha:(0:ℝ)<A.card:=by exact_mod_cast hA.card_pos
  have ha1:(1:ℝ)≤A.card:=by exact_mod_cast hA.card_pos
  have hV':(Fintype.card V:ℝ)+1≤(K+1)*A.card:=by nlinarith only [hV,ha1]
  have hU':(Fintype.card U:ℝ)+1≤(K+1)*A.card:=by nlinarith only [hU,ha1]
  have hcard:(Fintype.card V+1:ℝ)^h*(Fintype.card U+1:ℝ)^h≤
      ordinaryRowsCoefficient h K*(A.card:ℝ)^(2*h):=by
    calc
      _≤((K+1)*A.card)^h*((K+1)*A.card)^h:=by gcongr
      _=_:=by
        dsimp [ordinaryRowsCoefficient]
        simp only [mul_pow]
        rw [show 2*h=h+h by omega,pow_add]
        ring
  have herr:=linear_deviation_failure_exponential (ordinaryRowsCoefficient h K)
    ((4*(d:ℝ)+3)^2*(2*(2*(h:ℝ)+1))) ε (by positivity) hε (2*h) A.card hA.card_pos
    ((Fintype.card V+1:ℝ)^h*(Fintype.card U+1:ℝ)^h)
    ((4*(d:ℝ)+3)^2*(2*(2*(h:ℝ)+1)*A.card)) (by positivity) hcard (by positivity)
    (by exact le_of_eq (by ring))
  have hh:=rawOrdinaryRows_common_event P π d hd p hp hp1 q hq hQ s hs hS hnoshort
    A hA h j (ε*A.card) (by positivity)
  exact (sub_le_sub_left herr 1).trans hh
end Oberwolfach
