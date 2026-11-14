module

public import Oberwolfach.Neighbourhoods
public import Oberwolfach.EndpointRelativeCounts

@[expose] public section

/-! Mixed neighbourhood stability on fixed domains. The change bounds
refer to realised sets and are not multiplied by sampling probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
namespace Oberwolfach

 theorem common_common_comm {V I J:Type*} (A:Finset V) (S:Finset I) (T:Finset J)
    (N:I→Finset V) (M:J→Finset V):common (common A S N) T M=common (common A T M) S N:=by
  classical
  ext v
  simp only [common,Finset.mem_filter]
  tauto

theorem mixed_neighbourhood_stability {V I J:Type*} (A:Finset V) (S:Finset I) (T:Finset J)
    (N N':I→Finset V) (M M':J→Finset V) (a b:ℝ)
    (hN:∀ x∈S,((changed (N x) (N' x)).card:ℝ)≤a)
    (hM:∀ u∈T,((changed (M u) (M' u)).card:ℝ)≤b):
    |((common (common A S N') T M').card:ℝ)-(common (common A S N) T M).card|≤S.card*a+T.card*b:=by
  have hm:=neighbourhood_stability (common A S N') T M M' b hM
  have hn:=neighbourhood_stability (common A T M) S N N' a hN
  rw [←common_common_comm A S T N' M,←common_common_comm A S T N M] at hn
  have hh:=abs_sub_le
    (((common (common A S N') T M').card):ℝ)
    (((common (common A S N') T M).card):ℝ)
    (((common (common A S N) T M).card):ℝ)
  linarith only [hh,hm,hn]

theorem mixed_neighbourhood_target_stability {V I J:Type*} (A:Finset V) (S:Finset I) (T:Finset J)
    (N N':I→Finset V) (M M':J→Finset V) (a b μ e:ℝ)
    (hN:∀ x∈S,((changed (N x) (N' x)).card:ℝ)≤a)
    (hM:∀ u∈T,((changed (M u) (M' u)).card:ℝ)≤b)
    (ht:|((common (common A S N) T M).card:ℝ)-μ|≤e):
    |((common (common A S N') T M').card:ℝ)-μ|≤e+S.card*a+T.card*b:=by
  have hh:=target_stability (mixed_neighbourhood_stability A S T N N' M M' a b hN hM) ht
  simpa only [add_assoc] using hh

end Oberwolfach
