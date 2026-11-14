module

public import Oberwolfach.FiniteFibreCounts
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-! A bounded code for objects in each fibre; this records multiplicity
without choosing one representative and discarding the other objects. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_fibre_codes {A B : Type*} [Fintype A] [DecidableEq B]
    (f : A → B) (J : ℕ) (hJ : ∀ b,Fintype.card {a : A // f a=b} ≤ J) :
    ∃ code : A → Fin J,∀ a b,f a=f b → code a=code b → a=b := by
  have he (b : B) : Nonempty ({a : A // f a=b} ↪ Fin J) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_fin] using hJ b)
  let e := fun b => Classical.choice (he b)
  let code := fun a => e (f a) ⟨a,rfl⟩
  refine ⟨code,?_⟩
  intro a b hab hc
  have hb : f b=f a := hab.symm
  have hon (b₀ : B) (x : A) (hx : f x=b₀) : code x=e b₀ ⟨x,hx⟩ := by
    subst b₀
    rfl
  have hh : e (f a) ⟨a,rfl⟩=e (f a) ⟨b,hb⟩ := by
    rw [hon (f a) a rfl,hon (f a) b hb] at hc
    exact hc
  exact congrArg Subtype.val ((e (f a)).injective hh)

end Oberwolfach
