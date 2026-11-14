module

public import Oberwolfach.TransportMatrices
public import Oberwolfach.Brouwer

@[expose] public section

/-! Complementary-chain synchronization on a product of transportation
polytopes. The maps to be synchronized are continuous self-marginal maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def diagonalTransport {X : Type*} (m : X → ℝ) : X → X → ℝ :=
  fun x y => if x = y then m x else 0

theorem diagonalTransport_mem {X : Type*} [Fintype X]
    (m : X → ℝ) (hm : ∀ x, 0 ≤ m x) :
    diagonalTransport m ∈ transportMatrices m m := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    unfold diagonalTransport
    split_ifs
    · exact hm x
    · exact le_refl _
  · intro x
    simp [diagonalTransport]
  · intro y
    simp [diagonalTransport]

def walkTransport {I X : Type*} [Fintype X]
    (m : I → X → ℝ) (K : I → X → X → ℝ) (s : I → I) (i : I) :
    ℕ → X → X → ℝ
  | 0 => diagonalTransport (m i)
  | j + 1 => composeTransport (m (s i)) (K i) (walkTransport m K s (s i) j)

theorem walkTransport_mem {I X : Type*} [Fintype X]
    (m : I → X → ℝ) (K : I → X → X → ℝ) (s : I → I)
    (hm : ∀ i x, 0 < m i x)
    (hK : ∀ i, K i ∈ transportMatrices (m i) (m (s i))) (i : I) (j : ℕ) :
    walkTransport m K s i j ∈ transportMatrices (m i) (m (s^[j] i)) := by
  induction j generalizing i with
  | zero => exact diagonalTransport_mem (m i) (fun x => (hm i x).le)
  | succ j ih =>
    simpa only [walkTransport, Function.iterate_succ_apply] using
      composeTransport_mem (hK i) (ih (s i)) (hm (s i))

theorem walkTransport_continuous {I X : Type*} [Fintype I] [Fintype X]
    (m : I → X → ℝ) (s : I → I) (i : I) (j : ℕ) :
    Continuous (fun K : I → X → X → ℝ => walkTransport m K s i j) := by
  induction j generalizing i with
  | zero => exact continuous_const
  | succ j ih =>
    exact (composeTransport_continuous (m (s i))).comp
      ((continuous_apply i).prodMk (ih (s i)))

theorem transposeTransport_mem {X Y : Type*} [Fintype X] [Fintype Y]
    {m : X → ℝ} {n : Y → ℝ} {K : X → Y → ℝ}
    (hK : K ∈ transportMatrices m n) :
    (fun y x => K x y) ∈ transportMatrices n m :=
  ⟨fun y x => hK.1 x y, hK.2.2, hK.2.1⟩

def transportProduct {I X : Type*} [Fintype X]
    (m : I → X → ℝ) (s : I → I) : Set (I → X → X → ℝ) :=
  Set.pi Set.univ (fun i => transportMatrices (m i) (m (s i)))

theorem transportProduct_nonempty {I X : Type*} [Fintype I] [Fintype X]
    (m : I → X → ℝ) (s : I → I) (B : ℝ)
    (hB : 0 < B) (hm : ∀ i x, 0 ≤ m i x) (hms : ∀ i, ∑ x, m i x = B) :
    (transportProduct m s).Nonempty := by
  choose Q hQ using fun i => transportMatrices_nonempty (m i) (m (s i)) B
    (hm i) (hm (s i)) hB (hms i) (hms (s i))
  exact ⟨Q, fun i _ => hQ i⟩

theorem transportProduct_convex {I X : Type*} [Fintype I] [Fintype X]
    (m : I → X → ℝ) (s : I → I) :
    Convex ℝ (transportProduct m s) :=
  convex_pi (fun i _ => transportMatrices_convex (m i) (m (s i)))

theorem transportProduct_isCompact {I X : Type*} [Fintype I] [Fintype X]
    (m : I → X → ℝ) (s : I → I) :
    IsCompact (transportProduct m s) := by
  simpa [transportProduct, Set.pi] using
    isCompact_pi_infinite (fun i => transportMatrices_isCompact (m i) (m (s i)))

theorem complementary_transport_fixed_point {I X : Type*} [Fintype I] [Fintype X]
    (m : I → X → ℝ) (s : I → I) (j : ℕ)
    (hclose : ∀ i, s^[j] (s i) = i)
    (B : ℝ) (hB : 0 < B) (hm : ∀ i x, 0 < m i x) (hms : ∀ i, ∑ x, m i x = B)
    (H : transportProduct m s → I → X → X → ℝ)
    (hH : Continuous H)
    (hHm : ∀ Q i, H Q i ∈ transportMatrices (m i) (m (s i))) :
    ∃ Q : transportProduct m s, ∀ i x z,
      Q.val i x z = walkTransport m (H Q) s (s i) j z x := by
  let Φ : transportProduct m s → transportProduct m s := fun Q =>
    ⟨fun i x z => walkTransport m (H Q) s (s i) j z x, by
      intro i hi
      have hh := walkTransport_mem m (H Q) s hm (hHm Q) (s i) j
      rw [hclose i] at hh
      exact transposeTransport_mem hh⟩
  have hc : Continuous Φ := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    have hh := (walkTransport_continuous m s (s i) j).comp hH
    fun_prop
  obtain ⟨Q, hQ⟩ := compact_convex_fixed_point (transportProduct m s)
    (transportProduct_convex m s) (transportProduct_isCompact m s)
    (transportProduct_nonempty m s B hB (fun i x => (hm i x).le) hms) Φ hc
  refine ⟨Q, ?_⟩
  intro i x z
  exact (congrFun (congrFun (congrFun (congrArg Subtype.val hQ) i) x) z).symm

end Oberwolfach
