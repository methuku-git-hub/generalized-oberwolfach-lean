module

public import Oberwolfach.BoundaryReservationBalances

@[expose] public section

/-! A single physical sampling event controls the four marked balance
expressions at every root. The sets and coefficients are fixed before
exposure; later applications do not obtain a separate event per root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem boundary_reservation_balance_common_event (C M ε:ℝ) (hM:0<M) (hε:0<ε) (k q:ℕ):
    ∃ N:ℕ,∀ n:ℕ,N≤n→∀ (E R J:Type) [Fintype E] [DecidableEq E] [Fintype R] [Fintype J],
    (Fintype.card (R×J):ℝ)≤C*(n:ℝ)^k→∀ (A I:R→J→Finset E),
    (∀ r j,I r j⊆A r j)→(∀ r j,((A r j).card:ℝ)≤M*n)→
    ∀ (w:R→J→ℝ) (inner:R→Bool) (p:ℝ) (hp:0≤p) (hp1:p≤1),
    1-1/(n:ℝ)^q≤(FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).probability
      (fun σ=>∀ r,
        |(∑ j,w r j*(reservationRemaining (A r j) (I r j) (inner r) σ).card)-
          (if inner r then (1-p)*((∑ j,w r j*(A r j).card)-(∑ j,w r j*(I r j).card))
            else (∑ j,w r j*(A r j).card)-p*(∑ j,w r j*(I r j).card))|≤
          (∑ j,|w r j|)*(ε*n)):=by
  obtain ⟨N,hN⟩:=retained_coin_counts_common_event C M ε hM hε k q
  refine ⟨N,?_⟩
  intro n hn E R J _ _ _ _ hcount A I hI hA w inner p hp hp1
  let T:R×J→Finset E:=fun r=>if inner r.1 then A r.1 r.2\I r.1 r.2 else I r.1 r.2
  have hT (r:R×J):((T r).card:ℝ)≤M*n:=by
    apply le_trans _ (hA r.1 r.2)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    dsimp only [T]
    split_ifs
    · exact Finset.sdiff_subset
    · exact hI r.1 r.2
  have hevent:=hN n hn E (R×J) hcount T hT p hp hp1
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σ hσ r
  apply reservation_remaining_balance (A r) (I r) (hI r) (w r) p (ε*n) (inner r) σ
  intro j
  have h:=(hσ (r,j)).le
  cases hi:inner r <;> simpa only [T,hi,Bool.false_eq_true,ite_false,ite_true] using h
end Oberwolfach
