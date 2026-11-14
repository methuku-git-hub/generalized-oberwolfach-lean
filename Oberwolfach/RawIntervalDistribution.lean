module

public import Oberwolfach.RawIntervalGeometry
public import Oberwolfach.RawIntervalParameters
public import Oberwolfach.InterfaceFamilyRegularization

@[expose] public section

/-! Exact marginals of the original raw interval experiment, using the
activation, start-colour and label-colour laws separately. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V Γ Color : Type} [Fintype V] [DecidableEq V] [Fintype Γ] [Fintype Color]

def rawIntervalCoordinateLaw (d : ℕ) (hd : 2≤d)
    (q : Γ → ℝ) (hq : ∀ g,0≤q g) (hQ : ∑ g,q g≤1/8)
    (s : Color → ℝ) (hs : ∀ j,0≤s j)
    (hS : ∑ j,s j≤ intervalUncoveredProbability d (∑ g,q g)) :
    ∀ e : RawIntervalCoordinate V,FiniteLaw (RawIntervalCoordinateState Γ Color e)
  | Sum.inl _=>FiniteLaw.retentionCoin (intervalActivation d)
      (intervalActivation_bounds d hd).1.le (intervalActivation_bounds d hd).2.le
  | Sum.inr (Sum.inl _)=>rawIntervalStartLaw d hd q hq hQ
  | Sum.inr (Sum.inr _)=>rawIntervalLabelLaw d hd (∑ g,q g)
      (Finset.sum_nonneg (fun g _=>hq g)) hQ s hs hS

theorem finiteLaw_exclusive_union {Ω J : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (T : Finset J) (E : J → Ω → Prop)
    (hunique : ∀ ω,∀ i∈T,∀ j∈T,E i ω → E j ω → i=j) :
    μ.probability (fun ω=>∃ i∈T,E i ω)=∑ i∈T,μ.probability (E i) := by
  classical
  unfold FiniteLaw.probability
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases he : ∃ i∈T,E i ω
  · obtain ⟨i,hi,hei⟩ := he
    rw [if_pos ⟨i,hi,hei⟩]
    symm
    rw [Finset.sum_eq_single i]
    · exact if_pos hei
    · intro j hj hji
      exact if_neg (fun hej=>hji (hunique ω j hj i hi hej hei))
    · intro h;exact (h hi).elim
  · have hn (i : J) (hi : i∈T) : ¬E i ω := fun h=>he ⟨i,hi,h⟩
    rw [if_neg he]
    symm
    exact Finset.sum_eq_zero (fun i hi=>if_neg (hn i hi))

variable (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (q : Γ → ℝ) (hq : ∀ g,0≤q g) (hQ : ∑ g,q g≤1/8)
    (s : Color → ℝ) (hs : ∀ j,0≤s j)
    (hS : ∑ j,s j≤ intervalUncoveredProbability d (∑ g,q g))

local notation "μraw" => rawIntervalCoordinateLaw (V:=V) d hd q hq hQ s hs hS

include hd hq hQ hs hS

theorem rawIntervalKept_probability
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x) (a : V) :
    (FiniteLaw.pi μraw).probability (fun σ=>rawIntervalKept π d (fun x=>σ (Sum.inl x)) a)=
      isolatedStartProbability d := by
  let T := permutationWindow π d d a
  let R : Finset (RawIntervalCoordinate V) := T.image Sum.inl
  let value : RawIntervalOutcome V Γ Color := fun e=>match e with
    | Sum.inl x=>decide (x=a)
    | Sum.inr (Sum.inl _)=>none
    | Sum.inr (Sum.inr _)=>none
  have hself : a∈T := permutationWindow_self π d d a
  have hpred (σ : RawIntervalOutcome V Γ Color) :
      rawIntervalKept π d (fun x=>σ (Sum.inl x)) a ↔ ∀ e∈R,σ e=value e := by
    constructor
    · intro h e he
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he
      by_cases hx0 : x=a
      · subst x;simpa [value] using h.1
      · simpa [value,hx0] using h.2 x hx hx0
    · intro h
      refine ⟨?_,?_⟩
      · have hh:=h (Sum.inl a) (Finset.mem_image.mpr ⟨a,hself,rfl⟩)
        simpa [value] using hh
      · intro x hx hxa
        have hh:=h (Sum.inl x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)
        simpa [value,hxa] using hh
  have hp : (FiniteLaw.pi μraw).probability (fun σ=>rawIntervalKept π d (fun x=>σ (Sum.inl x)) a)=
      (FiniteLaw.pi μraw).expectation (patternValue R value) := by
    unfold FiniteLaw.probability FiniteLaw.expectation
    apply Finset.sum_congr rfl
    intro σ _
    rw [patternValue_indicator]
    simp only [hpred,mul_ite,mul_one,mul_zero]
  rw [hp,finiteLaw_expectation_pattern]
  dsimp only [R]
  rw [Finset.prod_image (by intro x _ y _ h;exact Sum.inl.inj h)]
  have hmass (x : V) : (μraw (Sum.inl x)).mass (value (Sum.inl x))=
      if x=a then intervalActivation d else 1-intervalActivation d := by
    by_cases hxa : x=a <;> simp [rawIntervalCoordinateLaw,FiniteLaw.retentionCoin,value,hxa]
  simp_rw [hmass]
  rw [← Finset.mul_prod_erase _ _ hself]
  simp only [if_pos rfl]
  have hprod : (∏ x∈T.erase a,if x=a then intervalActivation d else 1-intervalActivation d)=
      (1-intervalActivation d)^(2*d) := by
    have hc : T.card=2*d+1 := by
      simpa only [T,show d+d=2*d by omega] using permutationWindow_card π d d
        (by intro x k hk hkb;exact hnoshort x k hk (by omega)) a
    have herase : (T.erase a).card=2*d := by rw [Finset.card_erase_of_mem hself,hc];omega
    simp only [Finset.prod_congr rfl (fun x hx=>if_neg (Finset.mem_erase.mp hx).1),
      Finset.prod_const,herase]
  rw [hprod]
  rfl

theorem rawIntervalColouredStart_probability
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x) (a : V) (g : Γ) :
    (FiniteLaw.pi μraw).probability (fun σ=>rawIntervalColouredStart π d σ a g)=q g/(d:ℝ) := by
  let Acoords : Finset (RawIntervalCoordinate V) := Finset.univ.image Sum.inl
  let ecoord : RawIntervalCoordinate V := Sum.inr (Sum.inl a)
  have hdisj : Disjoint Acoords {ecoord} := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp he
    have hh:=Finset.mem_singleton.mp hf
    dsimp only [ecoord] at hh
    cases hh
  have hind := finiteLaw_disjoint_supported_events μraw Acoords {ecoord} hdisj
    (fun σ=>rawIntervalKept π d (fun x=>σ (Sum.inl x)) a)
    (fun σ=>σ ecoord=some g)
    (by
      intro σ τ hagree
      have hh : (fun x=>σ (Sum.inl x))=(fun x=>τ (Sum.inl x)) := by
        funext x;exact hagree (Sum.inl x) (Finset.mem_image.mpr ⟨x,Finset.mem_univ x,rfl⟩)
      rw [hh])
    (by intro σ τ hagree;rw [hagree ecoord (Finset.mem_singleton_self _)])
  change (FiniteLaw.pi μraw).probability (fun σ=>rawIntervalColouredStart π d σ a g)=_ at hind
  rw [rawIntervalKept_probability π d hd q hq hQ s hs hS hnoshort a,
    finiteLaw_pi_coordinate_probability μraw ecoord (some g)] at hind
  rw [hind]
  change isolatedStartProbability d*(q g/((d:ℝ)*isolatedStartProbability d))=q g/(d:ℝ)
  have hr:=isolatedStartProbability_pos d hd
  have hd0 : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  field_simp


theorem rawIntervalCovered_probability
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x) (x : V) (g : Γ) :
    (FiniteLaw.pi μraw).probability (fun σ=>rawIntervalCovered π d σ x g)=q g := by
  let T := permutationWindow π (d-1) 0 x
  have he (σ : RawIntervalOutcome V Γ Color) :
      rawIntervalCovered π d σ x g↔∃ a∈T,rawIntervalColouredStart π d σ a g := by
    constructor
    · rintro ⟨a,ha,hxa⟩
      exact ⟨a,(permutationWindow_dual π 0 (d-1) a x).mp hxa,ha⟩
    · rintro ⟨a,ha,hstart⟩
      exact ⟨a,hstart,(permutationWindow_dual π 0 (d-1) a x).mpr ha⟩
  have hh := finiteLaw_exclusive_union (FiniteLaw.pi μraw) T
    (fun a σ=>rawIntervalColouredStart π d σ a g)
    (by
      intro σ a ha b hb hsa hsb
      exact (rawInterval_coloured_start_unique π d σ x a b g g hsa hsb
        (permutationWindow_mono π (le_refl 0) (Nat.sub_le _ _) a
          ((permutationWindow_dual π 0 (d-1) a x).mpr ha))
        (permutationWindow_mono π (le_refl 0) (Nat.sub_le _ _) b
          ((permutationWindow_dual π 0 (d-1) b x).mpr hb))).1)
  simp only [← he] at hh
  rw [hh]
  have hc : T.card=d := by
    have ht:=permutationWindow_card π (d-1) 0
      (by intro y k hk hkb;exact hnoshort y k hk (by omega)) x
    simpa only [T,show d-1+0+1=d by omega] using ht
  simp_rw [rawIntervalColouredStart_probability π d hd q hq hQ s hs hS hnoshort]
  simp only [Finset.sum_const,hc,nsmul_eq_mul]
  have hd0 : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  field_simp

theorem rawIntervalBlocked_probability
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x) (x : V) :
    (FiniteLaw.pi μraw).probability (fun σ=>rawIntervalBlocked π d σ x)=
      (1+1/(d:ℝ))*(∑ g,q g) := by
  let T := permutationWindow π d 0 x
  let C : Finset (Γ×V) := Finset.univ.product T
  have he (σ : RawIntervalOutcome V Γ Color) :
      rawIntervalBlocked π d σ x↔∃ z∈C,rawIntervalColouredStart π d σ z.2 z.1 := by
    constructor
    · rintro ⟨g,a,ha,hxa⟩
      exact ⟨(g,a),Finset.mem_product.mpr ⟨Finset.mem_univ _,(permutationWindow_dual π 0 d a x).mp hxa⟩,ha⟩
    · rintro ⟨⟨g,a⟩,hz,hstart⟩
      exact ⟨g,a,hstart,(permutationWindow_dual π 0 d a x).mpr (Finset.mem_product.mp hz).2⟩
  have hh := finiteLaw_exclusive_union (FiniteLaw.pi μraw) C
    (fun z σ=>rawIntervalColouredStart π d σ z.2 z.1)
    (by
      intro σ i hi j hj hsi hsj
      have ha:=(Finset.mem_product.mp hi).2
      have hb:=(Finset.mem_product.mp hj).2
      have hu:=rawInterval_coloured_start_unique π d σ x i.2 j.2 i.1 j.1 hsi hsj
        ((permutationWindow_dual π 0 d i.2 x).mpr ha)
        ((permutationWindow_dual π 0 d j.2 x).mpr hb)
      exact Prod.ext hu.2 hu.1)
  simp only [← he] at hh
  rw [hh]
  have hc : T.card=d+1 := by
    simpa only [T,Nat.add_zero] using permutationWindow_card π d 0
      (by intro y k hk hkb;exact hnoshort y k hk (by omega)) x
  dsimp only [C]
  erw [Finset.sum_product]
  simp_rw [rawIntervalColouredStart_probability π d hd q hq hQ s hs hS hnoshort]
  simp only [Finset.sum_const,hc,nsmul_eq_mul,← Finset.mul_sum,← Finset.sum_div]
  have hd0 : (0:ℝ)<d := by exact_mod_cast (show 0<d by omega)
  push_cast
  field_simp

theorem rawIntervalUnblocked_probability
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x) (x : V) :
    (FiniteLaw.pi μraw).probability (fun σ=>¬rawIntervalBlocked π d σ x)=
      intervalUncoveredProbability d (∑ g,q g) := by
  have hh:=finiteLaw_probability_compl (FiniteLaw.pi μraw) (fun σ=>rawIntervalBlocked π d σ x)
  rw [rawIntervalBlocked_probability π d hd q hq hQ s hs hS hnoshort x] at hh
  unfold intervalUncoveredProbability
  linarith

theorem rawIntervalState_interval_probability
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x) (x : V) (g : Γ) :
    (FiniteLaw.pi μraw).probability (fun σ=>rawIntervalState π d σ x=some (Sum.inl g))=q g := by
  simp_rw [rawIntervalState_interval_iff]
  exact rawIntervalCovered_probability π d hd q hq hQ s hs hS hnoshort x g

theorem rawIntervalState_label_probability
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x) (x : V) (j : Color) :
    (FiniteLaw.pi μraw).probability (fun σ=>rawIntervalState π d σ x=some (Sum.inr j))=s j := by
  let Acoords : Finset (RawIntervalCoordinate V) :=
    Finset.univ.image Sum.inl ∪ Finset.univ.image (fun a : V=>Sum.inr (Sum.inl a))
  let ecoord : RawIntervalCoordinate V := Sum.inr (Sum.inr x)
  have hdisj : Disjoint Acoords {ecoord} := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    have hh:=Finset.mem_singleton.mp hf
    subst e
    simp [Acoords,ecoord] at he
  have hind := finiteLaw_disjoint_supported_events μraw Acoords {ecoord} hdisj
    (fun σ=>¬rawIntervalBlocked π d σ x) (fun σ=>σ ecoord=some j)
    (by
      intro σ τ hagree
      have hA (a : V) : σ (Sum.inl a)=τ (Sum.inl a) := by
        apply hagree;simp [Acoords]
      have hG (a : V) : σ (Sum.inr (Sum.inl a))=τ (Sum.inr (Sum.inl a)) := by
        apply hagree;simp [Acoords]
      dsimp only [rawIntervalBlocked,rawIntervalColouredStart,rawIntervalKept]
      simp_rw [hA,hG])
    (by intro σ τ hagree;rw [hagree ecoord (Finset.mem_singleton_self _)])
  simp_rw [rawIntervalState_label_iff]
  rw [hind,rawIntervalUnblocked_probability π d hd q hq hQ s hs hS hnoshort x,
    finiteLaw_pi_coordinate_probability μraw ecoord (some j)]
  change intervalUncoveredProbability d (∑ g,q g)*(s j/intervalUncoveredProbability d (∑ g,q g))=s j
  have hpos : 0 < intervalUncoveredProbability d (∑ g,q g) := by
    have hh:=intervalUncoveredProbability_lower d hd (∑ g,q g) (Finset.sum_nonneg (fun g _=>hq g)) hQ
    linarith
  field_simp

end Oberwolfach
