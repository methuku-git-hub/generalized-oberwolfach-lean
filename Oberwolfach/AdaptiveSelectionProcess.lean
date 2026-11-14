module

public import Oberwolfach.AdaptiveSelectionPotential

@[expose] public section

/-! Sequential selection with a history-dependent candidate family.
A finite average chooses the next candidate while preserving the common
potential for every fixed test; no independence of successive choices is used. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem adaptive_selection_process
    {I A State : Type*} [Fintype I] [Fintype A] [Nonempty A]
    (N B : ℕ) (active : Fin N→I→Prop) (q : ℝ) (hq : 0≤q)
    (counter : State→I→ℕ) (Good : ℕ→State→Prop) (initial : State)
    (hinit : Good 0 initial) (hzero : ∀ x,counter initial x=0)
    (hsmall : selectionPotential active q 0 (fun _=>0)<(2:ℝ)^B)
    (hstep : ∀ i : Fin N,∀ state,Good i.val state → (∀ x,counter state x<B) →
      ∃ next : A→State,∃ hit : A→I→Prop,
        (∀ a,Good (i.val+1) (next a)) ∧
        (∀ a x,counter (next a) x=counter state x+(if hit a x then 1 else 0)) ∧
        (∀ x,¬active i x → ∀ a,¬hit a x) ∧
        (∀ x,((Finset.univ.filter (fun a=>hit a x)).card:ℝ)≤q*Fintype.card A)) :
    ∃ state,Good N state ∧ ∀ x,counter state x<B := by
  have hex : ∀ k : ℕ,k≤N → ∃ state,Good k state ∧
      selectionPotential active q k (counter state)≤selectionPotential active q 0 (fun _=>0) := by
    intro k
    induction k with
    | zero=>
      intro hk
      refine ⟨initial,hinit,?_⟩
      have he : counter initial=(fun _=>0) := funext hzero
      rw [he]
    | succ k ih=>
      intro hk
      obtain ⟨state,hgood,hpot⟩ := ih (by omega)
      let i : Fin N := ⟨k,by omega⟩
      have hsafe := selectionPotential_counter_lt active q hq k B (counter state) (hpot.trans_lt hsmall)
      obtain ⟨next,hit,hnext,hcounter,hinactive,hcount⟩ := hstep i state hgood hsafe
      obtain ⟨a,ha⟩ := selectionPotential_step_choice active i q hq (counter state) hit hinactive hcount
      refine ⟨next a,hnext a,?_⟩
      have he : counter (next a)=(fun x=>counter state x+(if hit a x then 1 else 0)) := funext (hcounter a)
      rw [he]
      exact ha.trans hpot
  obtain ⟨state,hgood,hpot⟩ := hex N le_rfl
  exact ⟨state,hgood,selectionPotential_counter_lt active q hq N B (counter state) (hpot.trans_lt hsmall)⟩

end Oberwolfach
