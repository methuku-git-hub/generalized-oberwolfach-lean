module

public import Oberwolfach.BoundaryReservationBalanceEvent

@[expose] public section

/-! Reservation acts on physical coins, while the fixed incidence tests
may use auxiliary endpoints. The exact image identity below connects
those two representations before applying concentration. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem incident_reservation_image {A W E:Type} [DecidableEq A] [DecidableEq W] [DecidableEq E]
    (tail head:A→W) (coin:A↪E) (X:Finset W) (r:W) (T:Finset A)
    (hT:∀ a∈T,tail a=r∨head a=r) (σ:E→Bool):
    (T.filter (fun a=>¬((tail a∈X∧head a∈X)∨((tail a∈X∨head a∈X)∧σ (coin a)=true)))).image coin=
    reservationRemaining (T.image coin)
      ((T.filter (fun a=>(if tail a=r then head a else tail a)∈X)).image coin) (decide (r∈X)) σ:=by
  classical
  ext e
  by_cases hr:r∈X
  · simp only [reservationRemaining,hr,decide_true,ite_true,Finset.mem_filter,Finset.mem_sdiff,Finset.mem_image]
    constructor
    · rintro ⟨a,⟨ha,hkeep⟩,he⟩
      have hn:(if tail a=r then head a else tail a)∉X:=by
        by_cases ht:tail a=r
        · simp only [ht,ite_true];intro hh;exact hkeep (Or.inl ⟨ht.symm ▸ hr,hh⟩)
        · have hh:head a=r:=(hT a ha).resolve_left ht
          simp only [ht,ite_false];intro haX;exact hkeep (Or.inl ⟨haX,hh.symm ▸ hr⟩)
      have hcoin:σ (coin a)=false:=by
        have hit:tail a∈X∨head a∈X:=(hT a ha).imp (fun (h:tail a=r)=>h.symm ▸ hr) (fun (h:head a=r)=>h.symm ▸ hr)
        have hn:σ (coin a)≠true:=fun hc=>hkeep (Or.inr ⟨hit,hc⟩)
        simpa only [Bool.not_eq_true] using hn
      refine ⟨⟨⟨a,ha,he⟩,?_⟩,he ▸ hcoin⟩
      rintro ⟨z,⟨hz,hzX⟩,hzcoin⟩
      have hza:z=a:=coin.injective (hzcoin.trans he.symm)
      exact hn (hza ▸ hzX)
    · rintro ⟨⟨⟨a,ha,he⟩,hn⟩,hc⟩
      refine ⟨a,⟨ha,?_⟩,he⟩
      rintro (⟨ht,hh⟩|⟨_,hcoin⟩)
      · apply hn;refine ⟨a,⟨ha,?_⟩,he⟩;split_ifs <;> assumption
      · rw [he,hc] at hcoin;cases hcoin
  · simp only [reservationRemaining,hr,decide_false,Bool.false_eq_true,ite_false,
      Finset.mem_sdiff,Finset.mem_filter,Finset.mem_image]
    constructor
    · rintro ⟨a,⟨ha,hkeep⟩,he⟩
      refine ⟨⟨a,ha,he⟩,?_⟩
      rintro ⟨⟨z,⟨hz,hzX⟩,hzcoin⟩,hc⟩
      have hza:z=a:=coin.injective (hzcoin.trans he.symm)
      subst z
      have hit:tail a∈X∨head a∈X:=by split_ifs at hzX <;> tauto
      exact hkeep (Or.inr ⟨hit,he.symm ▸ hc⟩)
    · rintro ⟨⟨a,ha,he⟩,hn⟩
      refine ⟨a,⟨ha,?_⟩,he⟩
      rintro (⟨ht,hh⟩|⟨hit,hcoin⟩)
      · rcases hT a ha with h|h
        · exact hr (h ▸ ht)
        · exact hr (h ▸ hh)
      · apply hn
        refine ⟨⟨a,⟨ha,?_⟩,he⟩,he ▸ hcoin⟩
        by_cases ht:tail a=r
        · simpa only [ht,hr,false_or,ite_true] using hit
        · have hh:head a=r:=(hT a ha).resolve_left ht
          simpa only [ht,hh,hr,or_false,ite_false] using hit

theorem incident_reservation_balance_common_event (C M ε:ℝ) (hM:0<M) (hε:0<ε) (k q:ℕ):
    ∃ N:ℕ,∀ n:ℕ,N≤n→∀ (A W E R J:Type) [DecidableEq A] [DecidableEq W]
      [Fintype E] [DecidableEq E] [Fintype R] [Fintype J],
    (Fintype.card (R×J):ℝ)≤C*(n:ℝ)^k→
    ∀ (tail head:A→W) (coin:A↪E) (X:Finset W) (root:R→W) (T:R→J→Finset A),
    (∀ r j a,a∈T r j→tail a=root r∨head a=root r)→
    (∀ r j,((T r j).card:ℝ)≤M*n)→∀ (w:R→J→ℝ) (p:ℝ) (hp:0≤p) (hp1:p≤1),
    1-1/(n:ℝ)^q≤(FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).probability
      (fun σ=>∀ r,
        let I:=fun j=>(T r j).filter (fun a=>(if tail a=root r then head a else tail a)∈X);
        |(∑ j,w r j*((T r j).filter (fun a=>¬((tail a∈X∧head a∈X)∨
          ((tail a∈X∨head a∈X)∧σ (coin a)=true)))).card)-
          (if root r∈X then (1-p)*((∑ j,w r j*(T r j).card)-(∑ j,w r j*(I j).card))
            else (∑ j,w r j*(T r j).card)-p*(∑ j,w r j*(I j).card))|≤
          (∑ j,|w r j|)*(ε*n)):=by
  obtain ⟨N,hN⟩:=boundary_reservation_balance_common_event C M ε hM hε k q
  refine ⟨N,?_⟩
  intro n hn A W E R J _ _ _ _ _ _ hcount tail head coin X root T hT hsize w p hp hp1
  let I:R→J→Finset A:=fun r j=>(T r j).filter (fun a=>(if tail a=root r then head a else tail a)∈X)
  have hsub (r:R) (j:J):(I r j).image coin⊆(T r j).image coin:=Finset.image_subset_image (Finset.filter_subset _ _)
  have hsize' (r:R) (j:J):(((T r j).image coin).card:ℝ)≤M*n:=by
    rw [Finset.card_image_of_injective _ coin.injective];exact hsize r j
  have hevent:=hN n hn E R J hcount (fun r j=>(T r j).image coin) (fun r j=>(I r j).image coin)
    hsub hsize' w (fun r=>decide (root r∈X)) p hp hp1
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σ hσ r
  have hc (j:J):(reservationRemaining ((T r j).image coin) ((I r j).image coin)
      (decide (root r∈X)) σ).card=
      ((T r j).filter (fun a=>¬((tail a∈X∧head a∈X)∨((tail a∈X∨head a∈X)∧σ (coin a)=true)))).card:=by
    rw [←incident_reservation_image tail head coin X (root r) (T r j) (hT r j) σ,
      Finset.card_image_of_injective _ coin.injective]
  have h:=hσ r
  simp only [hc,Finset.card_image_of_injective _ coin.injective,decide_eq_true_eq] at h
  exact h
end Oberwolfach
