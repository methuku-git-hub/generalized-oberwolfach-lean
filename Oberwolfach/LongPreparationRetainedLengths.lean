module

public import Oberwolfach.LongPreparationFactorClassification

@[expose] public section
/-! A retained short length is an actual component length, hence it belongs to
the prescribed allowed set and is at least three. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_preparation_retained_length_allowed {n:ℕ} (hn:0<n)
    (F:SimpleGraph (Fin n)) (hF:F.IsRegularOfDegree 2) (S:Set ℕ)
    (hS:AllowedCycleLengths F S) (K:ℕ) (hK:0<K) (θ:ℝ) (hθ:0<θ)
    (i:Fin K)
    (hretain:θ/(100*(K:ℝ))≤
      ((Finset.univ.filter (fun v=>longPreparationCycleClass F hF K v=some i)).card:ℝ)/n):
    (3 : ℕ) ≤ (i.val + 1) ∧ (i.val + 1) ∈ S ∧
      ∃ v : Fin n, Fintype.card (F.connectedComponentMk v) = i.val + 1 := by
  have hK':(0:ℝ)<K:=by exact_mod_cast hK
  have hn':(0:ℝ)<n:=by exact_mod_cast hn
  have ht:0<θ/(100*(K:ℝ)):=by positivity
  have hfrac:0<((Finset.univ.filter (fun v=>longPreparationCycleClass F hF K v=some i)).card:ℝ)/n:=
    ht.trans_le hretain
  have hcard:0<(Finset.univ.filter (fun v=>longPreparationCycleClass F hF K v=some i)).card:=by
    by_contra h
    have hz:(Finset.univ.filter (fun v=>longPreparationCycleClass F hF K v=some i)).card=0:=by omega
    simp [hz] at hfrac
  obtain ⟨v,hv⟩:=Finset.card_pos.mp hcard
  have hclass:longPreparationCycleClass F hF K v=some i:=(Finset.mem_filter.mp hv).2
  have hlen:=((long_preparation_cycle_class F hF K v).2 i).1 hclass
  have hthree:3≤Fintype.card (F.connectedComponentMk v):=
    (component_regular_two_cycle_iso F hF (F.connectedComponentMk v)).1
  have hallowed: Fintype.card (F.connectedComponentMk v)∈S:=
    (AllowedCycleLengths_iff_component_orders F S).1 hS _
  rw [hlen] at hthree hallowed
  exact ⟨hthree,hallowed,v,hlen⟩
end Oberwolfach
