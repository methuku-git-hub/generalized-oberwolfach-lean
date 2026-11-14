module

public import Oberwolfach.MixedNeighbourhoodStability

@[expose] public section

/-! Only changes inside the fixed counting domain contribute to its
neighbourhood error. The tested roots may be outside that domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem common_inter_domain {V I:Type*} [Fintype V] [DecidableEq V]
    (A D:Finset V) (hDA:D⊆A) (S:Finset I) (N:I→Finset V):
    common D S (fun i=>A∩N i)=common D S N:=by
  ext v
  simp only [common,Finset.mem_filter,Finset.mem_inter]
  constructor
  · exact fun h=>⟨h.1,fun i hi=>(h.2 i hi).2⟩
  · exact fun h=>⟨h.1,fun i hi=>⟨hDA h.1,h.2 i hi⟩⟩

theorem fixed_domain_mixed_neighbourhood_stability {V I J:Type*} [Fintype V] [DecidableEq V]
    (A:Finset V) (S:Finset I) (T:Finset J) (N N':I→Finset V) (M M':J→Finset V)
    (a b:ℝ)
    (hN:∀ i∈S,((changed (A∩N i) (A∩N' i)).card:ℝ)≤a)
    (hM:∀ j∈T,((changed (A∩M j) (A∩M' j)).card:ℝ)≤b):
    |((common (common A S N') T M').card:ℝ)-(common (common A S N) T M).card|≤S.card*a+T.card*b:=by
  have he (N:I→Finset V) (M:J→Finset V):
      common (common A S (fun i=>A∩N i)) T (fun j=>A∩M j)=common (common A S N) T M:=by
    rw [common_inter_domain A A (Finset.Subset.refl _)]
    exact common_inter_domain A (common A S N) (fun v hv=>((mem_common_iff A S N v).mp hv).1) T M
  have hh:=mixed_neighbourhood_stability A S T (fun i=>A∩N i) (fun i=>A∩N' i)
    (fun j=>A∩M j) (fun j=>A∩M' j) a b hN hM
  simpa only [he] using hh

theorem fixed_domain_mixed_target_stability {V I J:Type*} [Fintype V] [DecidableEq V]
    (A:Finset V) (S:Finset I) (T:Finset J) (N N':I→Finset V) (M M':J→Finset V)
    (a b μ e:ℝ)
    (hN:∀ i∈S,((changed (A∩N i) (A∩N' i)).card:ℝ)≤a)
    (hM:∀ j∈T,((changed (A∩M j) (A∩M' j)).card:ℝ)≤b)
    (ht:|((common (common A S N) T M).card:ℝ)-μ|≤e):
    |((common (common A S N') T M').card:ℝ)-μ|≤e+S.card*a+T.card*b:=by
  have hh:=target_stability (fixed_domain_mixed_neighbourhood_stability A S T N N' M M' a b hN hM) ht
  simpa only [add_assoc] using hh

end Oberwolfach
