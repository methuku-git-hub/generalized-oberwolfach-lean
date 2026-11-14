module

public import Oberwolfach.ThreeIntervalCapacityAssembly
public import Oberwolfach.CyclicSectorFormula

@[expose] public section

/-! Cancellation of all endpoint matrices for one compatible three-interval
tuple. Only positive actual path probabilities are cancelled. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem threeIntervalSector_formula {X : Type*} [Fintype X] {L : Fin 3 → ℕ}
    (a : ∀ i, Fin (L i) → X → X → ℝ) (d : ∀ i, Fin (L i+1) → X → ℝ)
    (ρ : transportProduct (threeIntervalMarginal d) (finRotate 3) → ∀ i, (Fin (L i+1) → X) → ℝ)
    (Q : transportProduct (threeIntervalMarginal d) (finRotate 3))
    (hm : ∀ i x, 0 < threeIntervalMarginal d i x)
    (hK : ∀ i x z, 0 < threeIntervalResidualSystem a d ρ Q i x z)
    (hfixed : ∀ i x z, Q.val i x z=walkTransport (threeIntervalMarginal d)
      (threeIntervalResidualSystem a d ρ Q) (finRotate 3) (finRotate 3 i) 2 z x)
    (c : Fin 3) (p : ∀ i, Fin (L i+1) → X)
    (hp : ∀ i, p i (Fin.last (L i))=p (finRotate 3 i) 0)
    (η : ℝ) (hη : 0 < η)
    (hρ : ρ Q c (p c)=Q.val c (p c 0) (p c (Fin.last (L c)))*η) :
    threeIntervalSector a d ρ Q c p =
      η*(∏ i ∈ Finset.univ.erase c, halfResidualPathWeight (a i) (d i) (ρ Q i) (p i)) /
        ∏ j ∈ (Finset.univ.erase c).erase (finRotate 3 c), threeIntervalMarginal d j (p j 0) := by
  letI : Nonempty X := ⟨p 0 0⟩
  let S (i : Fin 3) := halfResidualPathWeight (a i) (d i) (ρ Q i) (p i)
  let w (i : Fin 3) := if i=c then ρ Q i (p i) else S i
  have hwc : w c=Q.val c (p c 0) (p (finRotate 3 c) 0)/η⁻¹ := by
    dsimp only [w]
    rw [if_pos rfl,hρ,hp]
    simp
  have hh := cyclic_sector_formula (threeIntervalMarginal d) (threeIntervalResidualSystem a d ρ Q)
    hm hK c (Q.val c) (hfixed c) (fun i => p i 0) w S η⁻¹ (inv_pos.mpr hη) hwc
    (fun i hi => by simp only [w,if_neg hi])
  have hsector : threeIntervalSector a d ρ Q c p =
      (∏ i ∈ Finset.univ.erase c, S i) /
        (η⁻¹ * ∏ j ∈ (Finset.univ.erase c).erase (finRotate 3 c), threeIntervalMarginal d j (p j 0)) := by
    convert hh using 1
    unfold threeIntervalSector
    simp only [hp]
    rfl
  rw [hsector]
  change _=η*(∏ i ∈ Finset.univ.erase c, S i)/_
  field_simp [hη.ne']

end Oberwolfach
