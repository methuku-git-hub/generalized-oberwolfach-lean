module

public import Oberwolfach.RawIntervalSelectedLabels
public import Oberwolfach.MarkedPotentialHubStability

@[expose] public section

/-! Actual compatible hubs for every separated marked cycle tuple. The
marked spoke is at position zero, and the other positions use the ordinary
spoke colour. All counts are evaluated in the same raw interval outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

def rawMarkedSpokes (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (g : Γ) (j : Color) : Bool→V→U→Prop
  | false,v,u=>rawIntervalFamilyState π d σ (v,u)=some (Sum.inr j)
  | true,v,u=>rawIntervalFamilyState π d σ (v,u)=some (Sum.inl g)

theorem rawMarkedHubs_count {m : ℕ} (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (g : Γ) (j : Color)
    (C : Fin (m+1)→V) (hC : Function.Injective C) :
    ((potentialMarkedHubs (rawMarkedSpokes π d σ g j) C).card:ℝ)=
      rawIntervalSelectedLabelCount π d σ (fun v=>if v=C 0 then Sum.inl g else Sum.inr j)
        (Finset.univ.image C) := by
  have heq : potentialMarkedHubs (rawMarkedSpokes π d σ g j) C=
      Finset.univ.filter (fun u=>∀ v∈Finset.univ.image C,
        rawIntervalFamilyState π d σ (v,u)=some (if v=C 0 then Sum.inl g else Sum.inr j)) := by
    ext u
    rw [potentialMarkedHubs_mem]
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro hu v hv
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
      refine Fin.cases ?_ (fun i=>?_) i
      · simpa only [ite_true,rawMarkedSpokes] using hu.1
      · have hne : C i.succ≠C 0 := fun hh=>Fin.succ_ne_zero i (hC hh)
        simpa only [if_neg hne,rawMarkedSpokes] using hu.2 i
    · intro hu
      refine ⟨?_,fun i=>?_⟩
      · have hh := hu (C 0) (Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩)
        simpa only [ite_true,rawMarkedSpokes] using hh
      · have hh := hu (C i.succ) (Finset.mem_image.mpr ⟨i.succ,Finset.mem_univ _,rfl⟩)
        have hne : C i.succ≠C 0 := fun hh=>Fin.succ_ne_zero i (hC hh)
        simpa only [if_neg hne,rawMarkedSpokes] using hh
  rw [heq,Finset.card_filter,Nat.cast_sum]
  simp only [rawIntervalSelectedLabelCount,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem rawMarkedHubs_pattern_mean {m : ℕ} (q : U→Γ→ℝ) (s : U→Color→ℝ)
    (g : Γ) (j : Color) (C : Fin (m+1)→V) (hC : Function.Injective C) (u : U) :
    (∏ v∈Finset.univ.image C,Sum.elim (q u) (s u) (if v=C 0 then Sum.inl g else Sum.inr j))=
      q u g*(s u j)^m := by
  rw [Finset.prod_image (by intro i _ k _ h;exact hC h)]
  rw [Fin.prod_univ_succ]
  have hne (i : Fin m) : C i.succ≠C 0 := fun hh=>Fin.succ_ne_zero i (hC hh)
  simp [hne]

theorem rawMarkedHubs_common_event
    (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (hm : 0<Fintype.card U) (m : ℕ) (g : Γ) (j : Color) (t : ℝ) (ht : 0<t) :
    1-(Fintype.card V:ℝ)^(m+1)*
      (2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(((m:ℝ)+1)*Fintype.card U))))≤
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ C : Fin (m+1)→V,PermutationSeparated π (3*d) C →
          |((potentialMarkedHubs (rawMarkedSpokes π d σ g j) C).card:ℝ)-
            ∑ u : U,q u g*(s u j)^m|<t) := by
  let I := {C : Fin (m+1)→V // PermutationSeparated π (3*d) C}
  let T (C : I) := Finset.univ.image C.val
  let col (C : I) (v : V) : Γ⊕Color := if v=C.val 0 then Sum.inl g else Sum.inr j
  have hsep : ∀ C : I,∀ x∈T C,∀ y∈T C,x≠y → ¬PermutationClose π (3*d) x y := by
    intro C x hx y hy hxy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hy
    exact C.property i k (fun hh=>hxy (congrArg C.val hh))
  have hnonempty (C : I) : (T C).Nonempty := ⟨C.val 0,Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩⟩
  have hsize (C : I) : (T C).card≤m+1 := by
    exact (Finset.card_image_le).trans (by simp)
  have hh := rawIntervalSelectedLabelCount_common_event π d hd q hq hQ s hs hS hnoshort hm
    col T hsep hnonempty (m+1) (by omega) hsize t ht
  have hcard : Fintype.card I≤(Fintype.card V)^(m+1) := by
    exact (Fintype.card_subtype_le _).trans_eq (by simp)
  have hcardR : (Fintype.card I:ℝ)≤(Fintype.card V:ℝ)^(m+1) := by exact_mod_cast hcard
  have hlower := mul_le_mul_of_nonneg_right hcardR
    (show 0≤2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((m+1:ℕ)*Fintype.card U))) by positivity)
  simp only [Nat.cast_add,Nat.cast_one] at hh hlower
  apply ((sub_le_sub_left hlower 1).trans hh).trans
  apply finiteLaw_probability_mono
  intro σ hσ C hC
  have hi := hσ ⟨C,hC⟩
  have hinj := permutationSeparated_injective π (3*d) C hC
  simpa only [T,col,rawMarkedHubs_pattern_mean q s g j C hinj,
    ← rawMarkedHubs_count π d σ g j C hinj] using hi

end Oberwolfach
