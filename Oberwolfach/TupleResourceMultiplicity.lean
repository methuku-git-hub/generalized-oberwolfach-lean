module

public import Oberwolfach.ResourceRestriction
public import Mathlib.Data.Fintype.CardEmbedding

@[expose] public section

/-! A resource family represented injectively by ordered c-tuples has
at most c^c representations on each c-element vertex set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

theorem tuple_resource_multiplicity (c : ℕ) (R : C → Finset V)
    (f : C → Fin c → V) (hf : Function.Injective f)
    (himage : ∀ C₀,R C₀=Finset.univ.image (f C₀))
    (hcard : ∀ C₀,(R C₀).card=c) (Y : Finset V) :
    Fintype.card {C₀ // R C₀=Y}≤c^c := by
  by_cases hY : ∃ C₀,R C₀=Y
  · obtain ⟨C₀,hC₀⟩ := hY
    have hYc : Y.card=c := by rw [← hC₀];exact hcard C₀
    let embed : {C₀ // R C₀=Y} → (Fin c → Y) := fun C₀ i =>
      ⟨f C₀.val i,by
        have hh : f C₀.val i∈R C₀.val := by
          rw [himage C₀.val]
          exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
        exact (congrArg (fun S : Finset V => f C₀.val i∈S) C₀.property).mp hh⟩
    have hi : Function.Injective embed := by
      intro C₀ C₁ he
      apply Subtype.ext
      apply hf
      funext i
      exact congrArg Subtype.val (congrFun he i)
    have hh := Fintype.card_le_of_injective embed hi
    simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,hYc] using hh
  · have hempty : IsEmpty {C₀ // R C₀=Y} := ⟨fun C₀ => hY ⟨C₀.val,C₀.property⟩⟩
    letI := hempty
    simp

end Oberwolfach
