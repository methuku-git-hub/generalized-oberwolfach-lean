module

public import Oberwolfach.IncidentReservationBalanceEvent

@[expose] public section

/-! One common event controls every supplied fixed incidence set. The
root index may include a direction and type; no resampling is performed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem incident_reservation_count_common_event (C M ε:ℝ) (hM:0<M) (hε:0<ε) (k q:ℕ):
    ∃ N:ℕ,∀ n:ℕ,N≤n→∀ (A W E R:Type) [DecidableEq A] [DecidableEq W]
      [Fintype E] [DecidableEq E] [Fintype R],
    (Fintype.card R:ℝ)≤C*(n:ℝ)^k→
    ∀ (tail head:A→W) (coin:A↪E) (X:Finset W) (root:R→W) (T:R→Finset A),
    (∀ r a,a∈T r→tail a=root r∨head a=root r)→
    (∀ r,((T r).card:ℝ)≤M*n)→∀ (p:ℝ) (hp:0≤p) (hp1:p≤1),
    1-1/(n:ℝ)^q≤(FiniteLaw.pi (fun _:E=>FiniteLaw.retentionCoin p hp hp1)).probability
      (fun σ=>∀ r,
        let I:=(T r).filter (fun a=>(if tail a=root r then head a else tail a)∈X);
        |(((T r).filter (fun a=>¬((tail a∈X∧head a∈X)∨
          ((tail a∈X∨head a∈X)∧σ (coin a)=true)))).card:ℝ)-
          (if root r∈X then (1-p)*((T r).card-I.card) else (T r).card-p*I.card)|≤ε*n):=by
  obtain ⟨N,hN⟩:=incident_reservation_balance_common_event C M ε hM hε k q
  refine ⟨N,?_⟩
  intro n hn A W E R _ _ _ _ _ hcount tail head coin X root T hT hsize p hp hp1
  have hcount':(Fintype.card (R×Unit):ℝ)≤C*(n:ℝ)^k:=by simpa only [Fintype.card_prod,Fintype.card_unique,mul_one] using hcount
  have hevent:=hN n hn A W E R Unit hcount' tail head coin X root (fun r _=>T r)
    (fun r _=>hT r) (fun r _=>hsize r) (fun _ _=>1) p hp hp1
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σ hσ r
  simpa only [Fintype.sum_unique,one_mul,abs_one,mul_one] using hσ r
end Oberwolfach
