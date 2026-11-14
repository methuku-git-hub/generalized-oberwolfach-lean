module

public import Oberwolfach.UniformFibres

@[expose] public section

/-! Ordered partitions represented by the cell containing each vertex.
The prescribed sizes are retained in the finite sample space. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

abbrev FixedPartition (V : Type*) [Fintype V] (k : ℕ) (d : Fin k → ℕ) :=
  {c : V → Fin k // ∀ a, Fintype.card {x : V // c x = a} = d a}

def fixedPartitionMap {V : Type*} [Fintype V] {k : ℕ} {d : Fin k → ℕ}
    (e : Equiv.Perm V) (P : FixedPartition V k d) : FixedPartition V k d :=
  ⟨fun x => P.1 (e.symm x), fun a =>
    (Fintype.card_congr (e.symm.subtypeEquiv (fun _ => Iff.rfl))).trans (P.2 a)⟩

theorem fixedPartitionMap_trans {V : Type*} [Fintype V] {k : ℕ} {d : Fin k → ℕ}
    (e f : Equiv.Perm V) (P : FixedPartition V k d) :
    fixedPartitionMap f (fixedPartitionMap e P) = fixedPartitionMap (e.trans f) P := rfl

theorem fixedPartitionMap_injective {V : Type*} [Fintype V] {k : ℕ} {d : Fin k → ℕ}
    (e : Equiv.Perm V) : Function.Injective (fixedPartitionMap (k := k) (d := d) e) := by
  intro P Q h
  apply Subtype.ext
  funext x
  have hh := congrFun (congrArg Subtype.val h) (e x)
  simpa only [fixedPartitionMap, e.symm_apply_apply] using hh

def fixedPartitionEquiv {V : Type*} [Fintype V] {k : ℕ} {d : Fin k → ℕ}
    (P Q : FixedPartition V k d) : Equiv.Perm V :=
  Equiv.ofFiberEquiv (fun a => Fintype.equivOfCardEq ((P.2 a).trans (Q.2 a).symm))

theorem fixedPartitionEquiv_map {V : Type*} [Fintype V] {k : ℕ} {d : Fin k → ℕ}
    (P Q : FixedPartition V k d) : fixedPartitionMap (fixedPartitionEquiv P Q) P = Q := by
  apply Subtype.ext
  funext x
  have h := Equiv.ofFiberEquiv_map
    (fun a => Fintype.equivOfCardEq ((P.2 a).trans (Q.2 a).symm))
    ((fixedPartitionEquiv P Q).symm x)
  simpa only [fixedPartitionEquiv, fixedPartitionMap, Equiv.apply_symm_apply] using h.symm

def permutationRightEquiv {V : Type*} (e : Equiv.Perm V) :
    Equiv.Perm V ≃ Equiv.Perm V where
  toFun σ := σ.trans e
  invFun σ := σ.trans e.symm
  left_inv σ := by ext x; simp
  right_inv σ := by ext x; simp

theorem finiteLaw_uniform_map_transitive
    {Ω Γ : Type*} [Fintype Ω] [Fintype Γ] [Nonempty Ω] [Nonempty Γ]
    (f : Ω → Γ)
    (hlift : ∀ x y, ∃ e : Ω ≃ Ω, ∀ ω, f (e ω) = y ↔ f ω = x) :
    (FiniteLaw.uniform Ω).map f = FiniteLaw.uniform Γ := by
  apply finiteLaw_eq_uniform_of_mass_constant
  intro x y
  obtain ⟨e, he⟩ := hlift x y
  change (∑ ω, if f ω = x then (1 : ℝ) / Fintype.card Ω else 0) =
    ∑ ω, if f ω = y then (1 : ℝ) / Fintype.card Ω else 0
  conv_rhs => rw [← e.sum_comp]
  simp only [he]

theorem fixedPartition_uniform {V : Type*} [Fintype V] {k : ℕ} {d : Fin k → ℕ}
    [Nonempty (FixedPartition V k d)] (P : FixedPartition V k d) :
    (FiniteLaw.uniform (Equiv.Perm V)).map (fun σ => fixedPartitionMap σ P) =
      FiniteLaw.uniform (FixedPartition V k d) := by
  apply finiteLaw_uniform_map_transitive
  intro Q R
  let e := fixedPartitionEquiv Q R
  refine ⟨permutationRightEquiv e, ?_⟩
  intro σ
  change fixedPartitionMap (σ.trans e) P = R ↔ fixedPartitionMap σ P = Q
  rw [← fixedPartitionMap_trans, ← fixedPartitionEquiv_map Q R]
  exact (fixedPartitionMap_injective e).eq_iff

theorem fixedPartition_nonempty {V : Type*} [Fintype V] {k : ℕ} (d : Fin k → ℕ)
    (hd : ∑ a, d a = Fintype.card V) : Nonempty (FixedPartition V k d) := by
  let e : (Σ a : Fin k, Fin (d a)) ≃ V := Fintype.equivOfCardEq (by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using hd)
  let c (x : V) : Fin k := (e.symm x).1
  refine ⟨⟨c, ?_⟩⟩
  intro a
  let g (j : Fin (d a)) : {x : V // c x = a} := ⟨e ⟨a,j⟩, by simp [c]⟩
  have hg : Function.Bijective g := by
    constructor
    · intro i j h
      have hh := e.injective (congrArg Subtype.val h)
      exact (Sigma.mk.inj_iff.mp hh).2 |> eq_of_heq
    · intro x
      have hx : (e.symm x.1).1 = a := x.2
      cases hq : e.symm x.1 with
      | mk b j =>
        have hb : b = a := by simpa only [hq] using hx
        subst b
        refine ⟨j, ?_⟩
        apply Subtype.ext
        change e ⟨a,j⟩ = x.1
        rw [← hq, e.apply_symm_apply]
  calc
    _ = Fintype.card (Fin (d a)) := by
      apply Fintype.card_congr
      exact (Equiv.ofBijective g hg).symm
    _ = d a := Fintype.card_fin _

end Oberwolfach
