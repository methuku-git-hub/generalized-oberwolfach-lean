module

public import Oberwolfach.RawProtectedPairHubLoss

@[expose] public section
/-! The common unassigned-pair and start-column events give an explicit
lower bound for hubs whose protected lists contain both endpoints. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_protected_pair_hubs_lower_from_counts
    {V U Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Fintype Color]
    (π:Equiv.Perm V) (d:ℕ) (hd:0<d) (σ:RawIntervalFamilyOutcome V U Bool Color)
    (r:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ false) r)
    (q:U→Bool→ℝ) (hQ:∀u,∑g,q u g≤1/8) (θ t:ℝ)
    (hpair:∀x y,x≠y→(5/32:ℝ)*θ^2*Fintype.card U-t≤rawIntervalUnassignedPairColumnCount π d σ x y Finset.univ)
    (hstart:∀v g,|rawIntervalStartColumnCount π d σ v g Finset.univ-∑u,q u g/(d:ℝ)|<t):
    ∀x y,x≠y→((5/32:ℝ)*θ^2-1/(4*(d:ℝ)))*Fintype.card U-5*t≤
      (rawProtectedPairHubs π d σ false true r J x y).card:=by
  have hdR:(0:ℝ)<d:=by exact_mod_cast hd
  have hqsum:(∑u:U,(q u false+q u true))≤(Fintype.card U:ℝ)/8:=by
    have hh:∀u,q u false+q u true≤(1/8:ℝ):=by
      intro u
      simpa [Fintype.sum_bool,add_comm] using hQ u
    have hs:=Finset.sum_le_sum (s:=Finset.univ) (fun u _=>hh u)
    simpa [Finset.sum_const,nsmul_eq_mul,div_eq_mul_inv] using hs
  have hmean:(∑u:U,q u false/(d:ℝ))+(∑u:U,q u true/(d:ℝ))≤
      (Fintype.card U:ℝ)/(8*(d:ℝ)):=by
    have hh:=div_le_div_of_nonneg_right hqsum hdR.le
    calc
      _ = ∑u:U,(q u false/(d:ℝ)+q u true/(d:ℝ)):=by rw [Finset.sum_add_distrib]
      _ = ∑u:U,(q u false+q u true)/(d:ℝ):=by
        apply Finset.sum_congr rfl
        intro u hu
        ring
      _ = (∑u:U,(q u false+q u true))/(d:ℝ):=by rw [Finset.sum_div]
      _ ≤ ((Fintype.card U:ℝ)/8)/(d:ℝ):=hh
      _ = _:=by ring
  intro x y hxy
  have h0:=(abs_lt.mp (hstart ((π^d).symm x) false)).2
  have h1:=(abs_lt.mp (hstart ((π^d).symm x) true)).2
  have h2:=(abs_lt.mp (hstart ((π^d).symm y) false)).2
  have h3:=(abs_lt.mp (hstart ((π^d).symm y) true)).2
  have hloss:=raw_protected_pair_hubs_loss_bound π d σ false true r J x y
  have hp:=hpair x y hxy
  have heq:(1/(4*(d:ℝ)))*(Fintype.card U:ℝ)=2*((Fintype.card U:ℝ)/(8*(d:ℝ))):=by ring
  nlinarith
end Oberwolfach
