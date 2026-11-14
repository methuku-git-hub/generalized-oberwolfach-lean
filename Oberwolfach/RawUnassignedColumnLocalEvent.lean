module

public import Oberwolfach.RawIntervalUnassignedColumnCount
public import Oberwolfach.CommonEvents

@[expose] public section
/-! Local unassigned-spoke columns on a prescribed vertex set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_interval_unassigned_column_local_event
    {V U Γ Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color]
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (A:Finset V) (J:Finset U) (t:ℝ) (ht:0<t):
    let μ:=FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
    1-2*(A.card:ℝ)*Real.exp (-2*t^2/(J.card:ℝ))≤
      μ.probability (fun σ=>∀v∈A,|rawIntervalUnassignedColumnCount π d σ v J-
        ∑u∈J,(1-(∑g,q u g)-(∑j,s u j))|<t):=by
  intro μ
  have hh:=finiteLaw_common_event_lower μ A
    (fun v σ=>t≤|rawIntervalUnassignedColumnCount π d σ v J-
      ∑u∈J,(1-(∑g,q u g)-(∑j,s u j))|)
    (fun _=>2*Real.exp (-2*t^2/(J.card:ℝ)))
    (fun v _=>rawIntervalUnassignedColumnCount_tail π d hd q hq hQ s hs hS hnoshort v J t ht.le)
  simp only [Finset.sum_const,nsmul_eq_mul,not_le] at hh
  convert hh using 1 <;> ring
end Oberwolfach
