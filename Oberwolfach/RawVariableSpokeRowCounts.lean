module

public import Oberwolfach.RawMarkedRestrictedSpokeDegrees

@[expose] public section
/-! Row counts of both raw spoke types with hub-dependent probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem raw_variable_spoke_row_counts_event
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hU:0<Fintype.card U) (g:Γ) (j:Color) (t:ℝ) (ht:0<t):
    1-4*(Fintype.card V:ℝ)*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(Fintype.card U)))≤
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
        (fun σ=>∀b v,|rawMarkedRestrictedSpokeRow π d σ g j b v Finset.univ-
          ∑u,if b then q u g else s u j|<t) :=by
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU
  have hrow:=rawIntervalSelectedLabelCountOn_common_event π d hd q hq hQ s hs hS hnoshort
    (Finset.univ:Finset U) Finset.univ_nonempty
    (fun (i:Bool×V) (_:V)=>if i.1 then Sum.inl g else Sum.inr j) (fun i=>{i.2})
    (by intro i x hx y hy hxy;simp only [Finset.mem_singleton] at hx hy;exact (hxy (hx.trans hy.symm)).elim)
    (fun i=>Finset.singleton_nonempty _) 1 (by omega) (by intro i;simp) t ht
  simp only [Fintype.card_prod,Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,one_mul,
    Finset.prod_singleton,Finset.card_univ] at hrow
  have he:2*(Fintype.card V:ℝ)*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*Fintype.card U)))=
      4*(Fintype.card V:ℝ)*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*Fintype.card U)):=by ring
  rw [he] at hrow
  apply hrow.trans
  apply finiteLaw_probability_mono
  intro σ hσ b v
  have hh:=hσ (b,v)
  cases b <;> simpa only [rawMarkedRestrictedSpokeRow,rawIntervalSelectedLabelCountOn,
    Finset.mem_singleton,forall_eq,Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,ite_false,ite_true] using hh
end Oberwolfach
