module

public import Oberwolfach.RawOrdinaryDomainIndexEvent
public import Oberwolfach.ExponentialConfigurationMargins

@[expose] public section
/-! Hub-domain tests have an exponential local-domain failure bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinaryIndicesCoefficient (h:ℕ) (K:ℝ):ℝ:=(K+1)^h
def ordinaryIndicesExponent (h d:ℕ) (ε:ℝ):ℝ:=2*ε^2/((4*(d:ℝ)+3)^2*((h:ℝ)+1))

theorem ordinary_indices_exponent_pos (h d:ℕ) (ε:ℝ) (hε:0<ε):0<ordinaryIndicesExponent h d ε:=by
  unfold ordinaryIndicesExponent
  positivity

theorem raw_ordinary_indices_exponential_event
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (p:ℝ) (hp:0≤p) (hp1:p≤1)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x k,0<k→k<2*d+1→(π^k) x≠x)
    (hF:permutationConflictGraph π (3*d)≤F)
    (B:Finset U) (hB:B.Nonempty) (K ε:ℝ) (hK:1≤K) (hε:0<ε)
    (hV:(Fintype.card V:ℝ)≤K*B.card) (h:ℕ) (j:Color) (pH:ℝ) (hj:∀u,s u j=pH):
    1-2*ordinaryIndicesCoefficient h K*(B.card:ℝ)^h*Real.exp (-ordinaryIndicesExponent h d ε*B.card)≤
      (FiniteLaw.pi (rawWheelLaw (fun _=>p) (fun _=>hp) (fun _=>hp1) d hd q hq hQ s hs hS)).probability
        (RawOrdinaryDomainIndices F π d h B pH j (ε*B.card)):=by
  have hb:(0:ℝ)<B.card:=by exact_mod_cast hB.card_pos
  have hb1:(1:ℝ)≤B.card:=by exact_mod_cast hB.card_pos
  have hV':(Fintype.card V:ℝ)+1≤(K+1)*B.card:=by nlinarith only [hV,hb1]
  have hcard:(Fintype.card V+1:ℝ)^h≤ordinaryIndicesCoefficient h K*(B.card:ℝ)^h:=by
    calc
      _≤((K+1)*B.card)^h:=by gcongr
      _=_:=by simp [ordinaryIndicesCoefficient,mul_pow]
  have herr:=linear_deviation_failure_exponential (ordinaryIndicesCoefficient h K)
    ((4*(d:ℝ)+3)^2*((h:ℝ)+1)) ε (by positivity) hε h B.card hB.card_pos
    ((Fintype.card V+1:ℝ)^h) ((4*(d:ℝ)+3)^2*((h+1:ℝ)*B.card))
    (by positivity) hcard (by positivity) (by exact le_of_eq (by ring))
  have hh:=rawOrdinaryDomainIndices_common_event F π (fun _=>p) (fun _=>hp) (fun _=>hp1)
    d hd q hq hQ s hs hS hnoshort hF B hB.card_pos h j pH hj (ε*B.card) (by positivity)
  exact (sub_le_sub_left herr 1).trans hh
end Oberwolfach
