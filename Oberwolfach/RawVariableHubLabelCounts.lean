module

public import Oberwolfach.RawIntervalNeighbourCounts

@[expose] public section
/-! One event controls every hub's ordinary-spoke count with its own
supplied (possibly nonconstant) density. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem raw_variable_hub_label_counts_event
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hn:0<Fintype.card V) (j:Color) (t:ℝ) (ht:0<t):
    1-(Fintype.card U:ℝ)*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card V))))≤
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
        (fun σ=>∀u,|rawIntervalNeighbourCount π d σ j Finset.univ {u}-
          (Fintype.card V:ℝ)*s u j|<t) := by
  have hh:=rawIntervalNeighbourCount_common_event π d hd q hq hQ s hs hS hnoshort hn j
    (fun _:U=>(Finset.univ:Finset V)) (fun u:U=>({u}:Finset U))
    (fun u=>Finset.singleton_nonempty u) 1 (by omega) (by intro u;simp) t ht
  simpa only [Finset.card_univ,Finset.prod_singleton,Nat.cast_one,one_mul] using hh
end Oberwolfach
