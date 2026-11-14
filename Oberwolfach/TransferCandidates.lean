module

public import Oberwolfach.TransferGreedyCounts

@[expose] public section

/-! Potential transfer candidates require both spokes at every free label.
The two spokes at the prescribed root are omitted until the final conversion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def transferRootCompletedSpokes {V U : Type*} (H : V → U → Prop) (v : V) : V → U → Prop :=
  fun z u=>z=v ∨ H z u

abbrev OrdinaryTransferCandidate {V U : Type*} {r : ℕ} (hr : 3 ≤ r)
    (P F : SimpleGraph V) (H : V → U → Prop) (v : V) (u u' : U) :=
  OrdinaryTransferConfiguration hr P F (transferRootCompletedSpokes H v) v u u'

theorem ordinary_transfer_candidates_many (r : ℕ) (hr : 3 ≤ r)
    (δ β : ℝ) (hδ : δ≤1) (hβ : 0<β)
    (hmargin : 0<1-((if r=3 then 3 else 2:ℕ):ℝ)*(1-δ)) :
    ∃ c : ℝ,0<c ∧ ∀ L : ℝ,0≤L → ∃ N : ℕ,
    ∀ (V U : Type) [Fintype V] [DecidableEq V],N≤Fintype.card V →
    ∀ (P F : SimpleGraph V) (A : Finset V) (v : V) (H : V → U → Prop) (u u' : U),
      β*Fintype.card V≤(A.card:ℝ) →
      (∀ z∈A∪{v},δ*(A.card:ℝ)≤((A∩P.neighborFinset z).card:ℝ)) →
      (∀ z,(F.degree z:ℝ)≤L) → (∀ z∈A,H z u ∧ H z u') →
      c*(Fintype.card V:ℝ)^(r^2)≤Fintype.card (OrdinaryTransferCandidate hr P F H v u u') := by
  obtain ⟨c,hc,hcN⟩ := ordinary_transfer_configurations_many r hr δ β hδ hβ hmargin
  refine ⟨c,hc,?_⟩
  intro L hL
  obtain ⟨N,hN⟩ := hcN L hL
  refine ⟨N,?_⟩
  intro V U _ _ hn P F A v H u u' hsize hP hF hA
  exact hN V U hn P F A v (transferRootCompletedSpokes H v) u u' hsize hP hF
    ⟨Or.inl rfl,Or.inl rfl⟩ (fun z hz=>⟨Or.inr (hA z hz).1,Or.inr (hA z hz).2⟩)

end Oberwolfach
