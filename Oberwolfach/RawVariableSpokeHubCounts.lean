module

public import Oberwolfach.RawMarkedRestrictedSpokeDegrees
public import Oberwolfach.RawMarkedSpokeDisjointness

@[expose] public section
/-! One raw event controls both marked and ordinary spoke counts at every
hub, with the hub-specific probabilities supplied by the construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem raw_variable_spoke_hub_counts_event
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hn:0<Fintype.card V) (g:Γ) (j:Color) (t:ℝ) (ht:0<t):
    1-4*(Fintype.card U:ℝ)*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card V)))≤
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
        (fun σ=>∀b u,|rawMarkedRestrictedSpokeCol π d σ g j b u Finset.univ-
          (if b then q u g else s u j)*(Fintype.card V:ℝ)|<t) := by
  have hh:=rawIntervalSelectedNeighbourCount_common_event π d hd q hq hQ s hs hS hnoshort hn
    (fun (i:Bool×U) (_:U)=>if i.1 then Sum.inl g else Sum.inr j)
    (fun _=>(Finset.univ:Finset V)) (fun i=>({i.2}:Finset U))
    (fun i=>Finset.singleton_nonempty _) 1 (by omega) (by intro i;simp) t ht
  simp only [Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,one_mul,
    Finset.prod_singleton] at hh
  have he:2*(Fintype.card U:ℝ)*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*Fintype.card V)))=
      4*(Fintype.card U:ℝ)*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*Fintype.card V)) := by ring
  rw [he] at hh
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ b u
  have h:=hσ (b,u)
  cases b <;> simpa only [rawMarkedRestrictedSpokeCol,rawIntervalSelectedNeighbourCount,
    Finset.mem_singleton,forall_eq,Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,
    ite_false,ite_true,mul_comm,Finset.card_univ] using h
theorem raw_spoke_hub_count_eq_card
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g:Γ) (j:Color) (b:Bool) (u:U):
    rawMarkedRestrictedSpokeCol π d σ g j b u Finset.univ =
      ((Finset.univ.filter (fun v=>rawMarkedSpokes π d σ g j b v u)).card:ℝ) := by
  unfold rawMarkedRestrictedSpokeCol
  cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,rawMarkedSpokes]
  all_goals rw [Finset.sum_boole]
end Oberwolfach
