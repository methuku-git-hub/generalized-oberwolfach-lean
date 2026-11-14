module

public import Oberwolfach.FiniteLocalLemma
public import Oberwolfach.FiniteCoordinateIndependence

@[expose] public section

/-! The local lemma for events with specified coordinate supports in the
original product probability space. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    {State : E → Type*} [∀ e,Fintype (State e)]

theorem finiteLaw_supported_avoidance_independent
    (μ : ∀ e,FiniteLaw (State e)) (A : I → (∀ e,State e) → Prop)
    (S : I → Finset E)
    (hs : ∀ i σ τ,(∀ e∈S i,σ e=τ e) → (A i σ ↔ A i τ))
    (i : I) (T : Finset I) (hd : ∀ j∈T,Disjoint (S i) (S j)) :
    (FiniteLaw.pi μ).probability (fun σ=>A i σ ∧ avoidsEvents A T σ)=
      (FiniteLaw.pi μ).probability (A i)*
        (FiniteLaw.pi μ).probability (avoidsEvents A T) := by
  apply finiteLaw_disjoint_supported_events μ (S i) (T.biUnion S)
  · apply Finset.disjoint_left.mpr
    intro e he ht
    obtain ⟨j,hj,hej⟩ := Finset.mem_biUnion.mp ht
    exact Finset.disjoint_left.mp (hd j hj) he hej
  · exact hs i
  · intro σ τ he
    apply forall_congr'
    intro j
    apply forall_congr'
    intro hj
    exact not_congr (hs j σ τ (fun e hej=>he e (Finset.mem_biUnion.mpr ⟨j,hj,hej⟩)))

theorem finiteLaw_coordinate_localLemma
    (μ : ∀ e,FiniteLaw (State e)) (A : I → (∀ e,State e) → Prop)
    (S : I → Finset E)
    (hs : ∀ i σ τ,(∀ e∈S i,σ e=τ e) → (A i σ ↔ A i τ))
    (N : I → Finset I)
    (hN : ∀ i j,i≠j → j∉N i → Disjoint (S i) (S j))
    (x : I → ℝ) (hx0 : ∀ i,0≤x i) (hx1 : ∀ i,x i<1)
    (hsmall : ∀ i,(FiniteLaw.pi μ).probability (A i)≤x i*∏ j∈N i,(1-x j)) :
    0<(FiniteLaw.pi μ).probability (fun σ=>∀ i,¬A i σ) := by
  have hind : ∀ i T,i∉T → Disjoint T (N i) →
      (FiniteLaw.pi μ).probability (fun σ=>A i σ ∧ avoidsEvents A T σ)=
        (FiniteLaw.pi μ).probability (A i)*
          (FiniteLaw.pi μ).probability (avoidsEvents A T) := by
    intro i T hi hdis
    apply finiteLaw_supported_avoidance_independent μ A S hs
    intro j hj
    exact hN i j (fun he=>hi (he ▸ hj))
      (fun hjN=>Finset.disjoint_left.mp hdis hj hjN)
  have he : avoidsEvents A Finset.univ=(fun σ=>∀ i,¬A i σ) := by
    funext σ
    exact propext (by simp [avoidsEvents])
  rw [← he]
  exact finiteLaw_localLemma (FiniteLaw.pi μ) A N x hx0 hx1 hind hsmall Finset.univ

theorem finiteLaw_positive_event_exists
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (A : Ω → Prop)
    (h : 0<μ.probability A) : ∃ ω,0<μ.mass ω ∧ A ω := by
  have hp : 0<∑ ω,if A ω then μ.mass ω else 0 := h
  obtain ⟨ω,_,hω⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun ω (_ : ω∈Finset.univ)=>show 0≤(if A ω then μ.mass ω else 0) from
      by split_ifs;exact μ.nonneg ω;exact le_refl _)).mp hp
  by_cases ha : A ω
  · exact ⟨ω,by simpa only [ha,ite_true] using hω,ha⟩
  · simp only [ha,ite_false,lt_self_iff_false] at hω

end Oberwolfach
