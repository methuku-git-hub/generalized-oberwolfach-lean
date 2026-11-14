module

public import Oberwolfach.MarkedVortexInnerBalanceScale

@[expose] public section
/-! For fixed positive contraction, the first inner level eventually exceeds
any prescribed local-colour concentration threshold. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_vortex_inner_eventually_large
    (ε:ℝ) (hε:0<ε) (Nlocal:ℕ):
    ∃N:ℕ,1≤N ∧ ∀{V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D mv:ℕ) (β:ℝ) (Q:Vortex U P D β ε mv),
      0<mv → N≤Fintype.card V → Nlocal≤(Q.extendedVertices 1).card :=by
  obtain ⟨N₀,hN₀⟩:=exists_nat_gt (2*(Nlocal:ℝ)/ε)
  refine ⟨max 1 N₀,by omega,?_⟩
  intro V U _ _ _ _ P D mv β Q hm hn
  have hnR:(N₀:ℝ)≤Fintype.card V:=by exact_mod_cast (show N₀≤Fintype.card V by omega)
  have hlarge:2*(Nlocal:ℝ)/ε<(Fintype.card V:ℝ):=hN₀.trans_le hnR
  have hlarge':2*(Nlocal:ℝ)<ε*(Fintype.card V:ℝ):=by
    simpa only [mul_comm] using (div_lt_iff₀ hε).1 hlarge
  have hinner:(ε/2)*(Fintype.card V:ℝ)≤(Q.extendedVertices 1).card:=by
    rw [Q.extendedVertices_eq (by have hh:=Q.length_pos;omega)]
    have hh:=(Q.consecutive_size_bounds hε hm Q.length_pos).1
    rw [Q.initial] at hh
    simp only [Finset.card_univ] at hh
    nlinarith
  have hreal:(Nlocal:ℝ)≤(Q.extendedVertices 1).card:=by linarith
  exact_mod_cast hreal
end Oberwolfach
