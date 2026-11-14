module

public import Oberwolfach.RawIntervalStartColumnCount

@[expose] public section
/-! Uniform start-column concentration for all vertices and colours. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem raw_interval_start_columns_event (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x) (t:ℝ) (ht:0≤t):
    1-2*(Fintype.card V:ℝ)*Fintype.card Γ*Real.exp (-2*t^2/Fintype.card U)≤
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
        (fun σ=>∀v g,|rawIntervalStartColumnCount π d σ v g Finset.univ-∑u,q u g/(d:ℝ)|<t):=by
  let μ:=FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  have hh:=finiteLaw_common_event_lower μ (Finset.univ:Finset (V×Γ))
    (fun z σ=>t≤|rawIntervalStartColumnCount π d σ z.1 z.2 Finset.univ-∑u,q u z.2/(d:ℝ)|)
    (fun _=>2*Real.exp (-2*t^2/Fintype.card U))
    (fun z _=>raw_interval_start_column_tail π d hd q hq hQ s hs hS hnoshort z.1 z.2 Finset.univ t ht)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Nat.cast_mul,nsmul_eq_mul,
    Finset.mem_univ,true_implies,not_le] at hh
  have hh':1-2*(Fintype.card V:ℝ)*Fintype.card Γ*Real.exp (-2*t^2/Fintype.card U)≤
      μ.probability (fun σ=>∀z:V×Γ,|rawIntervalStartColumnCount π d σ z.1 z.2 Finset.univ-∑u,q u z.2/(d:ℝ)|<t):=by
    convert hh using 1 <;> ring
  apply hh'.trans
  apply finiteLaw_probability_mono
  intro σ hσ v g
  exact hσ (v,g)
end Oberwolfach
