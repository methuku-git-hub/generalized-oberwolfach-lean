module

public import Oberwolfach.GraphPartitionGood
public import Oberwolfach.PartitionCyclicMatrices

@[expose] public section

/-! One event tests every vertex against every selected class, both in G
and after applying π to the class. It therefore controls the two sides of
every ordinary or twisted interface simultaneously. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def choosePermutation {V : Type*} (π : Equiv.Perm V) (b : Bool) : Equiv.Perm V :=
  if b then π else Equiv.refl V

def SuccessorPartitionGood {V I : Type*} [Fintype V] {k : ℕ} {d : Fin k → ℕ}
    (G : SimpleGraph V) (π : Equiv.Perm V) (a : I → Fin k)
    (m : ℕ) (D η : ℝ) (P : FixedPartition V k d) : Prop :=
  ∀ s b v, |(graphCellDegree G (choosePermutation π b) P v (a s) : ℝ) -
    D * ((m : ℝ) / Fintype.card V)| < η * m

theorem successorPartitionGood_probability {V I : Type*} [Fintype V] [Nonempty V] [Fintype I]
    {k : ℕ} {d : Fin k → ℕ} [Nonempty (FixedPartition V k d)]
    (G : SimpleGraph V) (π : Equiv.Perm V) (a : I ↪ Fin k)
    (m : ℕ) (hm : 0 < m) (hsize : ∀ s, d (a s) = m) (D ε η : ℝ)
    (hη : 0 < η) (hε : ε ≤ η / 2)
    (hdeg : ∀ v, |(G.degree v : ℝ) - D| ≤ ε * Fintype.card V) :
    1 - 4 * Fintype.card I * Fintype.card V * Real.exp (-η ^ 2 * m / 2) ≤
      (FiniteLaw.uniform (FixedPartition V k d)).probability
        (SuccessorPartitionGood G π a m D η) := by
  have h := graphPartition_common_good G (choosePermutation π) (Finset.univ.map a) m hm
    (by intro z hz; obtain ⟨s,_,rfl⟩ := Finset.mem_map.mp hz; exact hsize s)
    D ε η hη hε hdeg
  have he : (fun P : FixedPartition V k d => ∀ z ∈ Finset.univ.map a, ∀ b v,
      |(graphCellDegree G (choosePermutation π b) P v z : ℝ) -
        D * ((m : ℝ) / Fintype.card V)| < η * m) =
        SuccessorPartitionGood G π a m D η := by
    funext P
    apply propext
    constructor
    · intro hp s; exact hp (a s) (Finset.mem_map.mpr ⟨s,Finset.mem_univ _,rfl⟩)
    · intro hp z hz
      obtain ⟨s,_,rfl⟩ := Finset.mem_map.mp hz
      exact hp s
  rw [he] at h
  simp only [Finset.card_map, Finset.card_univ, Fintype.card_bool] at h
  convert h using 1 <;> ring

theorem successorPartitionGood_interface_degrees {V : Type*} [Fintype V]
    {ℓ k : ℕ} {d : Fin k → ℕ} (G : SimpleGraph V) (π : Equiv.Perm V)
    (b : Fin (ℓ + 2) → Bool)
    (a : Fin (ℓ + 2) ⊕ Fin (ℓ + 2) → Fin k) (m : ℕ) (D η : ℝ)
    (P : FixedPartition V k d) (hgood : SuccessorPartitionGood G π a m D η P) :
    (∀ s v, |(graphCellDegree G (Equiv.refl V) P v (a s) : ℝ) -
      D * ((m : ℝ) / Fintype.card V)| ≤ η * m) ∧
    (∀ i v, |(graphCellDegree G (choosePermutation π (b i)) P v
      (a (Sum.inl (finRotate (ℓ + 2) i))) : ℝ) -
      D * ((m : ℝ) / Fintype.card V)| ≤ η * m) := by
  constructor
  · intro s v
    exact (hgood s false v).le
  · intro i v
    exact (hgood (Sum.inl (finRotate (ℓ + 2) i)) (b i) v).le

end Oberwolfach
