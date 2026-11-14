module

public import Oberwolfach.PermutationClose
public import Oberwolfach.ShellPermutation

@[expose] public section

/-! Exact finite coordinate windows for the raw interval experiment. These
bounds do not skip vertices when a domain is restricted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

def permutationWindow (π : Equiv.Perm V) (left right : ℕ) (x : V) : Finset V :=
  Finset.univ.image (fun i : Fin (left+right+1)=>(π^i.val) ((π^left).symm x))

theorem permutationWindow_card_le (π : Equiv.Perm V) (left right : ℕ) (x : V) :
    (permutationWindow π left right x).card≤left+right+1 := by
  exact Finset.card_image_le.trans (by simp)

theorem permutationWindow_card (π : Equiv.Perm V) (left right : ℕ)
    (hnoshort : ∀ x k,0<k → k<left+right+1 → (π^k) x≠x) (x : V) :
    (permutationWindow π left right x).card=left+right+1 := by
  unfold permutationWindow
  rw [Finset.card_image_of_injective _
    (permutation_short_interval_injective π (left+right+1) hnoshort _)]
  simp

theorem permutation_power_cancel_image (π : Equiv.Perm V) (i j : ℕ) (x : V) :
    (π^i) ((π^j).symm x)=(π^j).symm ((π^i) x) := by
  apply (π^j).injective
  rw [Equiv.apply_symm_apply]
  rw [← Equiv.Perm.mul_apply,← pow_add,Nat.add_comm,pow_add,Equiv.Perm.mul_apply,
    Equiv.apply_symm_apply]

theorem permutationWindow_mem_iff (π : Equiv.Perm V) (left right : ℕ) (x y : V) :
    y∈permutationWindow π left right x ↔
      ∃ i : Fin (left+right+1),(π^i.val) x=(π^left) y := by
  simp only [permutationWindow,Finset.mem_image,Finset.mem_univ,true_and]
  apply exists_congr
  intro i
  rw [permutation_power_cancel_image]
  exact (π^left).symm_apply_eq

theorem permutationWindow_dual (π : Equiv.Perm V) (left right : ℕ) (x y : V) :
    y∈permutationWindow π left right x ↔ x∈permutationWindow π right left y := by
  rw [permutationWindow_mem_iff,permutationWindow_mem_iff]
  have hdir (l r : ℕ) (a b : V)
      (h : ∃ i : Fin (l+r+1),(π^i.val) a=(π^l) b) :
      ∃ j : Fin (r+l+1),(π^j.val) b=(π^r) a := by
    obtain ⟨i,hi⟩ := h
    refine ⟨⟨l+r-i.val,by omega⟩,?_⟩
    apply (π^l).injective
    calc
      _ = (π^(l+r-i.val)) ((π^l) b) := by
        rw [← Equiv.Perm.mul_apply,← pow_add,Nat.add_comm,pow_add,Equiv.Perm.mul_apply]
      _ = (π^(l+r-i.val)) ((π^i.val) a) := by rw [hi]
      _ = (π^(l+r)) a := by rw [← Equiv.Perm.mul_apply,← pow_add,Nat.sub_add_cancel (by omega)]
      _ = _ := by rw [pow_add,Equiv.Perm.mul_apply]
  exact ⟨hdir left right x y,hdir right left y x⟩

theorem permutationWindow_reverse_card_le (π : Equiv.Perm V) (left right : ℕ) (y : V) :
    (Finset.univ.filter (fun x=>y∈permutationWindow π left right x)).card≤left+right+1 := by
  have he : Finset.univ.filter (fun x=>y∈permutationWindow π left right x)=
      permutationWindow π right left y := by
    ext x;simp only [Finset.mem_filter,Finset.mem_univ,true_and,permutationWindow_dual]
  rw [he]
  simpa only [Nat.add_comm] using permutationWindow_card_le π right left y

theorem permutationClose_of_power_eq (π : Equiv.Perm V) (b i j : ℕ) (hi : i≤b) (hj : j≤b)
    (x y : V) (he : (π^i) x=(π^j) y) : PermutationClose π b x y := by
  by_cases hij : i=j
  · subst j;exact Or.inl ((π^i).injective he)
  rcases lt_or_gt_of_ne hij with hlt|hgt
  · refine Or.inr ⟨⟨j-i-1,by omega⟩,Or.inr ?_⟩
    apply (π^i).injective
    rw [← Equiv.Perm.mul_apply,← pow_add,show i+(j-i-1+1)=j by omega]
    exact he.symm
  · refine Or.inr ⟨⟨i-j-1,by omega⟩,Or.inl ?_⟩
    apply (π^j).injective
    rw [← Equiv.Perm.mul_apply,← pow_add,show j+(i-j-1+1)=i by omega]
    exact he

theorem permutationWindow_disjoint (π : Equiv.Perm V) (left right : ℕ) (x y : V)
    (hfar : ¬PermutationClose π (left+right) x y) :
    Disjoint (permutationWindow π left right x) (permutationWindow π left right y) := by
  apply Finset.disjoint_left.mpr
  intro z hx hy
  obtain ⟨i,hi⟩ := (permutationWindow_mem_iff π left right x z).mp hx
  obtain ⟨j,hj⟩ := (permutationWindow_mem_iff π left right y z).mp hy
  exact hfar (permutationClose_of_power_eq π (left+right) i.val j.val (by omega) (by omega)
    x y (hi.trans hj.symm))


theorem permutationWindow_self (π : Equiv.Perm V) (left right : ℕ) (x : V) :
    x∈permutationWindow π left right x := by
  apply (permutationWindow_mem_iff π left right x x).mpr
  exact ⟨⟨left,by omega⟩,rfl⟩

theorem permutationWindow_comp_subset (π : Equiv.Perm V) (l₁ r₁ l₂ r₂ : ℕ)
    (x y z : V) (hy : y∈permutationWindow π l₁ r₁ x)
    (hz : z∈permutationWindow π l₂ r₂ y) :
    z∈permutationWindow π (l₁+l₂) (r₁+r₂) x := by
  obtain ⟨i,hi⟩ := (permutationWindow_mem_iff π l₁ r₁ x y).mp hy
  obtain ⟨j,hj⟩ := (permutationWindow_mem_iff π l₂ r₂ y z).mp hz
  apply (permutationWindow_mem_iff π (l₁+l₂) (r₁+r₂) x z).mpr
  refine ⟨⟨i.val+j.val,by omega⟩,?_⟩
  change (π^(i.val+j.val)) x=(π^(l₁+l₂)) z
  calc
    _ = (π^j.val) ((π^i.val) x) := by rw [Nat.add_comm,pow_add,Equiv.Perm.mul_apply]
    _ = (π^j.val) ((π^l₁) y) := by rw [hi]
    _ = (π^l₁) ((π^j.val) y) := by rw [← Equiv.Perm.mul_apply,← pow_add,Nat.add_comm,pow_add,Equiv.Perm.mul_apply]
    _ = (π^l₁) ((π^l₂) z) := by rw [hj]
    _ = _ := by rw [pow_add,Equiv.Perm.mul_apply]

theorem permutationWindow_mono (π : Equiv.Perm V) {l₁ r₁ l₂ r₂ : ℕ}
    (hl : l₁≤l₂) (hr : r₁≤r₂) (x : V) :
    permutationWindow π l₁ r₁ x⊆permutationWindow π l₂ r₂ x := by
  intro y hy
  obtain ⟨i,hi⟩ := (permutationWindow_mem_iff π l₁ r₁ x y).mp hy
  apply (permutationWindow_mem_iff π l₂ r₂ x y).mpr
  refine ⟨⟨i.val+(l₂-l₁),by omega⟩,?_⟩
  change (π^(i.val+(l₂-l₁))) x=(π^l₂) y
  calc
    _ = (π^(l₂-l₁)) ((π^i.val) x) := by rw [Nat.add_comm,pow_add,Equiv.Perm.mul_apply]
    _ = (π^(l₂-l₁)) ((π^l₁) y) := by rw [hi]
    _ = _ := by rw [← Equiv.Perm.mul_apply,← pow_add,Nat.sub_add_cancel hl]

end Oberwolfach
