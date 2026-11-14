module

public import Oberwolfach.BernoulliFactorCommonEvent

@[expose] public section

/-! One independent-vertex event for a polynomial family of fixed sets.
The sets and their indices precede the sample; graph roots may be external. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem bernoulli_fixed_sets_common_event (C ε:ℝ) (hC:0<C) (hε:0<ε) (k q:ℕ):
    ∃ N:ℕ,∀ (V J:Type) [Fintype V] [DecidableEq V] [Fintype J],N≤Fintype.card V→
      (Fintype.card J:ℝ)≤C*(Fintype.card V:ℝ)^k→∀ (A:J→Finset V)
      (p:ℝ) (hp:0≤p) (hp1:p≤1),
      1-1/(Fintype.card V:ℝ)^q≤
        (FiniteLaw.pi (fun _:V=>FiniteLaw.retentionCoin p hp hp1)).probability
          (fun σ=>∀ j,|(((A j)∩bernoulliVertexSet σ).card:ℝ)-p*(A j).card|<ε*Fintype.card V):=by
  obtain ⟨N,hN⟩:=constant_deviation_failure_eventually_small C 1 ε (by norm_num) hε k q
  refine ⟨max 1 N,?_⟩
  intro V J _ _ _ hn hJ A p hp hp1
  have hn0:0<Fintype.card V:=by omega
  let μ:=FiniteLaw.pi (fun _:V=>FiniteLaw.retentionCoin p hp hp1)
  let bad:J→(V→Bool)→Prop:=fun j σ=>ε*Fintype.card V≤
    |(((A j)∩bernoulliVertexSet σ).card:ℝ)-p*(A j).card|
  have hbad:μ.probability (fun σ=>∃ j,bad j σ)≤(Fintype.card J:ℝ)*
      (2*Real.exp (-2*ε^2/(1/(Fintype.card V:ℝ)))):=by
    have hh:=finiteLaw_union_bound μ Finset.univ bad
    simp only [Finset.mem_univ,true_and,exists_const] at hh
    apply hh.trans
    calc
      _≤∑ _:J,2*Real.exp (-2*ε^2/(1/(Fintype.card V:ℝ))):=
        Finset.sum_le_sum (fun j _=>bernoulli_domain_size_tail (A j) hn0 p hp hp1 ε hε)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hs:=hN (Fintype.card V) (by omega) (Fintype.card J) (Nat.cast_nonneg _) hJ
  have hc:=finiteLaw_probability_compl μ (fun σ=>∃ j,bad j σ)
  have hnnot:(fun σ=>¬∃ j,bad j σ)=(fun σ=>∀ j,
      |(((A j)∩bernoulliVertexSet σ).card:ℝ)-p*(A j).card|<ε*Fintype.card V):=by
    funext σ;simp only [bad,not_exists,not_le]
  rw [hnnot] at hc
  linarith only [hbad,hs,hc]

end Oberwolfach
