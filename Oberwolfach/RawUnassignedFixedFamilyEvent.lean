module

public import Oberwolfach.RawIntervalUnassignedHubRestricted
public import Oberwolfach.CommonEvents

@[expose] public section
/-! Uniform concentration on an arbitrary fixed finite family of test sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_interval_unassigned_fixed_family_event
    {V U Γ Color I:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color] [Fintype I]
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hn:0<Fintype.card V) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (A:I→Finset V) (t:ℝ) (ht:0<t):
    1-2*(Fintype.card U:ℝ)*(Fintype.card I:ℝ)*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card V:ℝ)))≤
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability (fun σ=>
      ∀u i,|rawIntervalUnassignedHubCountOn π d σ u (A i)-(A i).card*(1-(∑g,q u g)-(∑j,s u j))|<t):=by
  let μ:=FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  have hh:=finiteLaw_common_event_lower μ (Finset.univ:Finset (U×I))
    (fun z σ=>t≤|rawIntervalUnassignedHubCountOn π d σ z.1 (A z.2)-(A z.2).card*(1-(∑g,q z.1 g)-(∑j,s z.1 j))|)
    (fun _=>2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card V:ℝ)))) (by
      intro z _
      have ht':=rawIntervalUnassignedHubCountOn_tail π d hd q hq hQ s hs hS hn z.1 (A z.2) t ht
      rw [rawIntervalUnassignedHubCountOn_expectation π d hd q hq hQ s hs hS hnoshort z.1 (A z.2)] at ht'
      exact ht')
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Nat.cast_mul,nsmul_eq_mul,Finset.mem_univ,true_implies,not_le,Prod.forall] at hh
  convert hh using 1 <;> ring
end Oberwolfach
