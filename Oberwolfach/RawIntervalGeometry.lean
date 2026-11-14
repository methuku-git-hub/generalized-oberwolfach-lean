module

public import Oberwolfach.PermutationWindows
public import Oberwolfach.ResourcePatternConcentration

@[expose] public section

/-! Deterministic interval assignment before retention. Coordinates for
activations, start colours and ordinary label colours remain distinct. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V Γ Color : Type} [Fintype V] [DecidableEq V]

theorem permutationClose_of_power_gap (π : Equiv.Perm V) (b i j : ℕ)
    (hi : i ≤ j+b) (hj : j ≤ i+b) (x y : V) (he : (π^i) x=(π^j) y) :
    PermutationClose π b x y := by
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

theorem permutationWindow_symmetric_iff (π : Equiv.Perm V) (d : ℕ) (x y : V) :
    y∈permutationWindow π d d x ↔ PermutationClose π d x y := by
  constructor
  · intro hy
    obtain ⟨i,hi⟩ := (permutationWindow_mem_iff π d d x y).mp hy
    exact permutationClose_of_power_gap π d i.val d (by omega) (by omega) x y hi
  · rintro (rfl|⟨j,hj|hj⟩)
    · exact permutationWindow_self π d d x
    · apply (permutationWindow_mem_iff π d d x y).mpr
      refine ⟨⟨d+(j.val+1),by omega⟩,?_⟩
      change (π^(d+(j.val+1))) x=(π^d) y
      rw [pow_add,Equiv.Perm.mul_apply,hj]
    · apply (permutationWindow_mem_iff π d d x y).mpr
      refine ⟨⟨d-(j.val+1),by omega⟩,?_⟩
      change (π^(d-(j.val+1))) x=(π^d) y
      rw [← hj,← Equiv.Perm.mul_apply,← pow_add,Nat.sub_add_cancel (by omega)]

abbrev RawIntervalCoordinate (V : Type) := V⊕V⊕V

abbrev RawIntervalCoordinateState (Γ Color : Type) : RawIntervalCoordinate V → Type
  | Sum.inl _=>Bool
  | Sum.inr (Sum.inl _)=>Option Γ
  | Sum.inr (Sum.inr _)=>Option Color

instance rawIntervalCoordinateStateFintype [Fintype Γ] [Fintype Color]
    (e : RawIntervalCoordinate V) : Fintype (RawIntervalCoordinateState Γ Color e) := by
  cases e with
  | inl a => exact inferInstanceAs (Fintype Bool)
  | inr e =>
    cases e with
    | inl a => exact inferInstanceAs (Fintype (Option Γ))
    | inr a => exact inferInstanceAs (Fintype (Option Color))

abbrev RawIntervalOutcome (V Γ Color : Type) :=
  ∀ e : RawIntervalCoordinate V,RawIntervalCoordinateState Γ Color e

def rawIntervalKept (π : Equiv.Perm V) (d : ℕ) (A : V → Bool) (a : V) : Prop :=
  A a=true ∧ ∀ b∈permutationWindow π d d a,b≠a → A b=false

def rawIntervalColouredStart (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalOutcome V Γ Color) (a : V) (g : Γ) : Prop :=
  rawIntervalKept π d (fun x=>σ (Sum.inl x)) a ∧ σ (Sum.inr (Sum.inl a))=some g

def rawIntervalCovered (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalOutcome V Γ Color) (x : V) (g : Γ) : Prop :=
  ∃ a,rawIntervalColouredStart π d σ a g ∧ x∈permutationWindow π 0 (d-1) a

def rawIntervalBlocked (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalOutcome V Γ Color) (x : V) : Prop :=
  ∃ g a,rawIntervalColouredStart π d σ a g ∧ x∈permutationWindow π 0 d a

def rawIntervalState (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalOutcome V Γ Color) (x : V) : Option (Γ⊕Color) :=
  if h : ∃ g,rawIntervalCovered π d σ x g then some (Sum.inl (Classical.choose h))
  else if rawIntervalBlocked π d σ x then none
  else (σ (Sum.inr (Sum.inr x))).map Sum.inr

theorem rawIntervalKept_separated (π : Equiv.Perm V) (d : ℕ) (A : V → Bool)
    (a b : V) (ha : rawIntervalKept π d A a) (hb : rawIntervalKept π d A b) (hne : a≠b) :
    ¬PermutationClose π d a b := by
  intro hclose
  have hh := ha.2 b ((permutationWindow_symmetric_iff π d a b).mpr hclose) (Ne.symm hne)
  rw [hb.1] at hh
  cases hh

theorem rawInterval_extended_disjoint (π : Equiv.Perm V) (d : ℕ) (A : V → Bool)
    (a b : V) (ha : rawIntervalKept π d A a) (hb : rawIntervalKept π d A b) (hne : a≠b) :
    Disjoint (permutationWindow π 0 d a) (permutationWindow π 0 d b) := by
  apply permutationWindow_disjoint π 0 d a b
  simpa only [zero_add] using rawIntervalKept_separated π d A a b ha hb hne

theorem rawInterval_coloured_start_unique (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalOutcome V Γ Color) (x a b : V) (g h : Γ)
    (ha : rawIntervalColouredStart π d σ a g) (hb : rawIntervalColouredStart π d σ b h)
    (hxa : x∈permutationWindow π 0 d a) (hxb : x∈permutationWindow π 0 d b) :
    a=b ∧ g=h := by
  have he : a=b := by
    by_contra hne
    exact Finset.disjoint_left.mp (rawInterval_extended_disjoint π d _ a b ha.1 hb.1 hne) hxa hxb
  subst b
  exact ⟨rfl,Option.some.inj (ha.2.symm.trans hb.2)⟩

theorem rawIntervalCovered_unique (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalOutcome V Γ Color) (x : V) (g h : Γ)
    (hg : rawIntervalCovered π d σ x g) (hh : rawIntervalCovered π d σ x h) : g=h := by
  obtain ⟨a,ha,hxa⟩ := hg
  obtain ⟨b,hb,hxb⟩ := hh
  exact (rawInterval_coloured_start_unique π d σ x a b g h ha hb
    (permutationWindow_mono π (le_refl 0) (Nat.sub_le _ _) a hxa)
    (permutationWindow_mono π (le_refl 0) (Nat.sub_le _ _) b hxb)).2

theorem rawIntervalCovered_blocked (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalOutcome V Γ Color) (x : V) (g : Γ)
    (hg : rawIntervalCovered π d σ x g) : rawIntervalBlocked π d σ x := by
  obtain ⟨a,ha,hxa⟩ := hg
  exact ⟨g,a,ha,permutationWindow_mono π (le_refl 0) (Nat.sub_le _ _) a hxa⟩

theorem rawIntervalState_interval_iff (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalOutcome V Γ Color) (x : V) (g : Γ) :
    rawIntervalState π d σ x=some (Sum.inl g) ↔ rawIntervalCovered π d σ x g := by
  unfold rawIntervalState
  split_ifs with hg hb
  · have hh := Classical.choose_spec hg
    constructor
    · intro he
      have he' : Classical.choose hg=g := Sum.inl.inj (Option.some.inj he)
      exact he' ▸ hh
    · intro he
      rw [rawIntervalCovered_unique π d σ x _ _ hh he]
  · constructor
    · intro he;cases he
    · intro he;exact (hg ⟨g,he⟩).elim
  · constructor
    · intro he
      cases hc : σ (Sum.inr (Sum.inr x)) <;> simp [hc] at he
    · intro he;exact (hg ⟨g,he⟩).elim

theorem rawIntervalState_label_iff (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalOutcome V Γ Color) (x : V) (j : Color) :
    rawIntervalState π d σ x=some (Sum.inr j) ↔
      ¬rawIntervalBlocked π d σ x ∧ σ (Sum.inr (Sum.inr x))=some j := by
  unfold rawIntervalState
  split_ifs with hg hb
  · have hh := rawIntervalCovered_blocked π d σ x _ (Classical.choose_spec hg)
    simp only [hh,not_true_eq_false,false_and,Option.some.injEq,Sum.inl_ne_inr]
  · simp [hb]
  · simp only [hb,not_false_eq_true,true_and]
    cases hc : σ (Sum.inr (Sum.inr x)) with
    | none =>
      change (none : Option (Γ⊕Color))=some (Sum.inr j) ↔ (none : Option Color)=some j
      constructor <;> intro he <;> cases he
    | some a =>
      change some (Sum.inr (α:=Γ) a)=some (Sum.inr j) ↔ some a=some j
      exact ⟨fun he=>congrArg some (Sum.inr.inj (Option.some.inj he)),
        fun he=>congrArg (fun z : Color=>some (Sum.inr (α:=Γ) z)) (Option.some.inj he)⟩


def rawIntervalStateCoordinates (π : Equiv.Perm V) (d : ℕ) (x : V) : Finset (RawIntervalCoordinate V) :=
  (permutationWindow π (2*d) d x).image Sum.inl ∪
    (permutationWindow π d 0 x).image (fun a=>Sum.inr (Sum.inl a)) ∪
      {Sum.inr (Sum.inr x)}

theorem rawIntervalStateCoordinates_card (π : Equiv.Perm V) (d : ℕ) (x : V) :
    (rawIntervalStateCoordinates π d x).card≤4*d+3 := by
  have h₁ := Finset.card_union_le
    ((permutationWindow π (2*d) d x).image (Sum.inl (β:=V⊕V)))
    ((permutationWindow π d 0 x).image (fun a=>Sum.inr (Sum.inl a)))
  have h₂ := Finset.card_union_le
    (((permutationWindow π (2*d) d x).image (Sum.inl (β:=V⊕V))) ∪
      ((permutationWindow π d 0 x).image (fun a=>Sum.inr (Sum.inl a))))
    {Sum.inr (Sum.inr x)}
  have h₃ := (Finset.card_image_le (s:=permutationWindow π (2*d) d x)
    (f:=Sum.inl (β:=V⊕V))).trans (permutationWindow_card_le π (2*d) d x)
  have h₄ := (Finset.card_image_le (s:=permutationWindow π d 0 x)
    (f:=fun a : V=>Sum.inr (α:=V) (Sum.inl (β:=V) a))).trans (permutationWindow_card_le π d 0 x)
  simp only [Finset.card_singleton] at h₂
  unfold rawIntervalStateCoordinates
  omega

theorem rawIntervalStateCoordinates_reverse_card (π : Equiv.Perm V) (d : ℕ)
    (e : RawIntervalCoordinate V) :
    (Finset.univ.filter (fun x=>e∈rawIntervalStateCoordinates π d x)).card≤4*d+3 := by
  cases e with
  | inl a =>
    have he : Finset.univ.filter (fun x=>Sum.inl a∈rawIntervalStateCoordinates π d x)=
        Finset.univ.filter (fun x=>a∈permutationWindow π (2*d) d x) := by
      ext x;simp [rawIntervalStateCoordinates]
    rw [he]
    exact (permutationWindow_reverse_card_le π (2*d) d a).trans (by omega)
  | inr e =>
    cases e with
    | inl a =>
      have he : Finset.univ.filter (fun x=>Sum.inr (Sum.inl a)∈rawIntervalStateCoordinates π d x)=
          Finset.univ.filter (fun x=>a∈permutationWindow π d 0 x) := by
        ext x;simp [rawIntervalStateCoordinates]
      rw [he]
      exact (permutationWindow_reverse_card_le π d 0 a).trans (by omega)
    | inr a =>
      have he : Finset.univ.filter (fun x=>Sum.inr (Sum.inr a)∈rawIntervalStateCoordinates π d x)={a} := by
        ext x;simp [rawIntervalStateCoordinates,eq_comm]
      rw [he,Finset.card_singleton]
      omega

theorem rawIntervalState_supported (π : Equiv.Perm V) (d : ℕ)
    (σ τ : RawIntervalOutcome V Γ Color) (x : V)
    (hagree : ∀ e∈rawIntervalStateCoordinates π d x,σ e=τ e) :
    rawIntervalState π d σ x=rawIntervalState π d τ x := by
  have hcol (a : V) (g : Γ) (hxa : x∈permutationWindow π 0 d a) :
      rawIntervalColouredStart π d σ a g↔rawIntervalColouredStart π d τ a g := by
    have ha := (permutationWindow_dual π 0 d a x).mp hxa
    have ha0 : a∈permutationWindow π (2*d) d x :=
      permutationWindow_mono π (by omega) (by omega) x ha
    have hact (z : V) (hz : z∈permutationWindow π (2*d) d x) : σ (Sum.inl z)=τ (Sum.inl z) := by
      apply hagree
      simp only [rawIntervalStateCoordinates,Finset.mem_union,Finset.mem_image,Finset.mem_singleton]
      exact Or.inl (Or.inl ⟨z,hz,rfl⟩)
    have hstart : σ (Sum.inr (Sum.inl a))=τ (Sum.inr (Sum.inl a)) := by
      apply hagree
      simp only [rawIntervalStateCoordinates,Finset.mem_union,Finset.mem_image,Finset.mem_singleton]
      exact Or.inl (Or.inr ⟨a,ha,rfl⟩)
    dsimp only [rawIntervalColouredStart,rawIntervalKept]
    rw [hact a ha0,hstart]
    apply and_congr_left
    intro _
    apply and_congr_right
    intro _
    apply forall_congr'
    intro z
    apply forall_congr'
    intro hz
    apply forall_congr'
    intro _
    have hz0 := permutationWindow_comp_subset π d 0 d d x a z ha hz
    have hz1 : z∈permutationWindow π (2*d) d x := by convert hz0 using 1 <;> congr 1 <;> omega
    rw [hact z hz1]
  have hcov (g : Γ) : rawIntervalCovered π d σ x g↔rawIntervalCovered π d τ x g := by
    unfold rawIntervalCovered
    apply exists_congr
    intro a
    by_cases hxa : x∈permutationWindow π 0 (d-1) a
    · simp only [hxa,and_true]
      exact hcol a g (permutationWindow_mono π (le_refl 0) (Nat.sub_le _ _) a hxa)
    · simp only [hxa,and_false]
  have hblock : rawIntervalBlocked π d σ x↔rawIntervalBlocked π d τ x := by
    unfold rawIntervalBlocked
    apply exists_congr
    intro g
    apply exists_congr
    intro a
    by_cases hxa : x∈permutationWindow π 0 d a
    · simp only [hxa,and_true];exact hcol a g hxa
    · simp only [hxa,and_false]
  have hlab : σ (Sum.inr (Sum.inr x))=τ (Sum.inr (Sum.inr x)) := by
    apply hagree
    simp [rawIntervalStateCoordinates]
  have heq (j : Γ⊕Color) : rawIntervalState π d σ x=some j↔rawIntervalState π d τ x=some j := by
    cases j with
    | inl g => rw [rawIntervalState_interval_iff,rawIntervalState_interval_iff,hcov]
    | inr j => rw [rawIntervalState_label_iff,rawIntervalState_label_iff,hblock,hlab]
  cases hσ : rawIntervalState π d σ x with
  | none =>
    cases hτ : rawIntervalState π d τ x with
    | none => rfl
    | some j => have hh:=(heq j).mpr hτ;rw [hσ] at hh;cases hh
  | some j => exact ((heq j).mp hσ).symm


def rawIntervalCoordinateVertex : RawIntervalCoordinate V → V
  | Sum.inl a=>a
  | Sum.inr (Sum.inl a)=>a
  | Sum.inr (Sum.inr a)=>a

theorem rawIntervalStateCoordinates_vertex (π : Equiv.Perm V) (d : ℕ) (x : V)
    (e : RawIntervalCoordinate V) (he : e∈rawIntervalStateCoordinates π d x) :
    rawIntervalCoordinateVertex e∈permutationWindow π (2*d) d x := by
  cases e with
  | inl a => simpa [rawIntervalStateCoordinates,rawIntervalCoordinateVertex] using he
  | inr e =>
    cases e with
    | inl a =>
      have ha : a∈permutationWindow π d 0 x := by simpa [rawIntervalStateCoordinates] using he
      exact permutationWindow_mono π (by omega) (by omega) x ha
    | inr a =>
      have ha : a=x := by simpa [rawIntervalStateCoordinates] using he
      subst a
      exact permutationWindow_self π (2*d) d x

theorem rawIntervalStateCoordinates_disjoint (π : Equiv.Perm V) (d : ℕ) (x y : V)
    (hfar : ¬PermutationClose π (3*d) x y) :
    Disjoint (rawIntervalStateCoordinates π d x) (rawIntervalStateCoordinates π d y) := by
  have hd : Disjoint (permutationWindow π (2*d) d x) (permutationWindow π (2*d) d y) := by
    apply permutationWindow_disjoint
    simpa only [show 2*d+d=3*d by omega] using hfar
  apply Finset.disjoint_left.mpr
  intro e hx hy
  exact Finset.disjoint_left.mp hd (rawIntervalStateCoordinates_vertex π d x e hx)
    (rawIntervalStateCoordinates_vertex π d y e hy)

theorem rawIntervalState_separated_probability [Fintype Γ] [Fintype Color]
    (π : Equiv.Perm V) (d : ℕ)
    (μ : ∀ e : RawIntervalCoordinate V,FiniteLaw (RawIntervalCoordinateState Γ Color e))
    (S : Finset V) (hsep : ∀ x∈S,∀ y∈S,x≠y → ¬PermutationClose π (3*d) x y)
    (value : V → Option (Γ⊕Color)) :
    (FiniteLaw.pi μ).probability (fun σ=>∀ x∈S,rawIntervalState π d σ x=value x)=
      ∏ x∈S,(FiniteLaw.pi μ).probability (fun σ=>rawIntervalState π d σ x=value x) := by
  apply finiteLaw_disjoint_supported_family μ (rawIntervalStateCoordinates π d)
    (fun x σ=>rawIntervalState π d σ x=value x)
    (fun x σ τ hagree=>by rw [rawIntervalState_supported π d σ τ x hagree])
  intro x hx y hy hne
  exact rawIntervalStateCoordinates_disjoint π d x y (hsep x hx y hy hne)

end Oberwolfach
