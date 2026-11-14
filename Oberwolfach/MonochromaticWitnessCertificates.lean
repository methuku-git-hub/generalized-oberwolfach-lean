module

public import Oberwolfach.FiniteWitnessCertificates

@[expose] public section

/-! Witnesses for different colours cannot use the same coordinate when
every witness coordinate carries the colour it certifies. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem monochromatic_witness_certificate
    {I C Ω : Type*} [Fintype I] [Fintype C]
    (P : C → (I → Ω) → Prop) (S : (I → Ω) → C → Finset I)
    (colour : Ω → C) (L : Finset C) {k : ℕ}
    (hL : ∀ x c,P c x → c∈L)
    (hsize : ∀ x c,P c x → (S x c).card≤k)
    (hcolour : ∀ x c,P c x → ∀ i∈S x c,colour (x i)=c)
    (hwitness : ∀ x c,P c x → ∀ y,(∀ i∈S x c,x i=y i) → P c y) :
    HasCoordinateCertificateBound
      (fun x=>((Finset.univ.filter (fun c=>P c x)).card : ℝ))
      1 ((k : ℝ)*(L.card : ℝ)) := by
  classical
  apply finiteWitness_coordinate_certificate P S
  · intro x
    exact_mod_cast Finset.card_le_card (show Finset.univ.filter (fun c=>P c x)⊆L from
      fun c hc=>hL x c (Finset.mem_filter.mp hc).2)
  · exact hsize
  · intro x i
    have hsub : Finset.univ.filter (fun c=>P c x ∧ i∈S x c)⊆{colour (x i)} := by
      intro c hc
      have h := (Finset.mem_filter.mp hc).2
      exact Finset.mem_singleton.mpr (hcolour x c h.1 i h.2).symm
    have hc := Finset.card_le_card hsub
    simpa only [Finset.card_singleton,Nat.cast_one] using
      (show ((Finset.univ.filter (fun c=>P c x ∧ i∈S x c)).card : ℝ)≤
        ({colour (x i)} : Finset C).card by exact_mod_cast hc)
  · exact hwitness

end Oberwolfach
