module

public import Oberwolfach.SymmetricLocalLemma

@[expose] public section

/-! An explicit local-lemma bound from coordinate supports and the number
of events involving each coordinate. No independence of overlapping events
is asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_coordinate_localLemma_degree
    {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    {State : E → Type*} [∀ e,Fintype (State e)]
    (μ : ∀ e,FiniteLaw (State e)) (A : I → (∀ e,State e) → Prop)
    (S : I → Finset E)
    (hs : ∀ i σ τ,(∀ e∈S i,σ e=τ e) → (A i σ ↔ A i τ))
    {r s : ℕ} (hr : 0<r) (hspos : 0<s)
    (hsize : ∀ i,(S i).card≤r)
    (hinc : ∀ e,(Finset.univ.filter (fun i=>e∈S i)).card≤s)
    (hp : ∀ i,(FiniteLaw.pi μ).probability (A i)≤1/(4*((r*s : ℕ) : ℝ))) :
    ∃ σ,0<(FiniteLaw.pi μ).mass σ ∧ ∀ i,¬A i σ := by
  classical
  let N : I → Finset I := fun i=>
    Finset.univ.filter (fun j=>j≠i ∧ ¬Disjoint (S i) (S j))
  have hdeg (i : I) : (N i).card≤r*s := by
    have hsub : N i⊆(S i).biUnion (fun e=>Finset.univ.filter (fun j=>e∈S j)) := by
      intro j hj
      have hdis := (Finset.mem_filter.mp hj).2.2
      obtain ⟨e,he,hj⟩ := Finset.not_disjoint_iff.mp hdis
      exact Finset.mem_biUnion.mpr ⟨e,he,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
    calc
      (N i).card ≤ ((S i).biUnion (fun e=>Finset.univ.filter (fun j=>e∈S j))).card :=
        Finset.card_le_card hsub
      _ ≤ ∑ e∈S i,(Finset.univ.filter (fun j=>e∈S j)).card := Finset.card_biUnion_le
      _ ≤ ∑ _e∈S i,s := Finset.sum_le_sum (fun e _=>hinc e)
      _ = (S i).card*s := by simp
      _ ≤ r*s := Nat.mul_le_mul_right _ (hsize i)
  have hind : ∀ i T,i∉T → Disjoint T (N i) →
      (FiniteLaw.pi μ).probability (fun σ=>A i σ ∧ avoidsEvents A T σ)=
        (FiniteLaw.pi μ).probability (A i)*
          (FiniteLaw.pi μ).probability (avoidsEvents A T) := by
    intro i T hi hdis
    apply finiteLaw_supported_avoidance_independent μ A S hs
    intro j hj
    by_contra hn
    have hji : j≠i := fun he=>hi (he ▸ hj)
    have hjN : j∈N i := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hji,hn⟩
    exact Finset.disjoint_left.mp hdis hj hjN
  have hpos := finiteLaw_symmetric_localLemma (FiniteLaw.pi μ) A N
    (Nat.mul_pos hr hspos) hdeg hind hp Finset.univ
  obtain ⟨σ,hσ,hA⟩ := finiteLaw_positive_event_exists (FiniteLaw.pi μ)
    (avoidsEvents A Finset.univ) hpos
  exact ⟨σ,hσ,by simpa [avoidsEvents] using hA⟩

end Oberwolfach
