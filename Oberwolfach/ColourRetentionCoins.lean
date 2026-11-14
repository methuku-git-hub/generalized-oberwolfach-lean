module

public import Oberwolfach.TentativeColouring

@[expose] public section

/-! Colour-dependent retention coins, sampled together with the colour
at each vertex. Different vertices, not the two components at one vertex,
are the independent coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def FiniteLaw.withCoin {C : Type*} [Fintype C] (μ : FiniteLaw C)
    (a : C → ℝ) (ha : ∀ c,0≤a c ∧ a c≤1) : FiniteLaw (C×Bool) where
  mass x := μ.mass x.1*(if x.2 then a x.1 else 1-a x.1)
  nonneg x := mul_nonneg (μ.nonneg _) (by
    cases x.2 <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact sub_nonneg.mpr (ha _).2
    · exact (ha _).1)
  total := by
    rw [Fintype.sum_prod_type]
    have he (c : C) : (∑ b : Bool,μ.mass c*(if b then a c else 1-a c))=μ.mass c := by
      rw [Fintype.sum_bool]
      simp only [Bool.false_eq_true,ite_false,ite_true]
      ring
    simp_rw [he]
    exact μ.total

theorem finiteLaw_withCoin_colour {C : Type*} [Fintype C]
    (μ : FiniteLaw C) (a : C → ℝ) (ha : ∀ c,0≤a c ∧ a c≤1) (c : C) :
    (μ.withCoin a ha).probability (fun x=>x.1=c)=μ.mass c := by
  classical
  unfold FiniteLaw.probability FiniteLaw.withCoin
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,Bool.false_eq_true,ite_false,ite_true]
  have he (d : C) :
      (if d=c then μ.mass d*a d else 0)+
        (if d=c then μ.mass d*(1-a d) else 0)=if d=c then μ.mass d else 0 := by
    split_ifs <;> ring
  simp_rw [he]
  simp

theorem finiteLaw_withCoin_not_colour {C : Type*} [Fintype C]
    (μ : FiniteLaw C) (a : C → ℝ) (ha : ∀ c,0≤a c ∧ a c≤1) (c : C) :
    (μ.withCoin a ha).probability (fun x=>x.1≠c)=1-μ.mass c := by
  have hh := finiteLaw_probability_compl (μ.withCoin a ha) (fun x=>x.1=c)
  rw [finiteLaw_withCoin_colour] at hh
  linarith

theorem finiteLaw_withCoin_success {C : Type*} [Fintype C]
    (μ : FiniteLaw C) (a : C → ℝ) (ha : ∀ c,0≤a c ∧ a c≤1) (c : C) :
    (μ.withCoin a ha).probability (fun x=>x.1=c ∧ x.2=true)=μ.mass c*a c := by
  have he (x : C×Bool) : (x.1=c ∧ x.2=true) ↔ x=(c,true) := by
    constructor
    · rintro ⟨h₁,h₂⟩
      exact Prod.ext h₁ h₂
    · rintro rfl
      exact ⟨rfl,rfl⟩
  rw [finiteLaw_probability_congr _ _ _ he,finiteLaw_probability_point]
  rfl

def coinColourSurvives {V C : Type*} (G : SimpleGraph V)
    (σ : V → C×Bool) (v : V) : Prop :=
  (σ v).2=true ∧ tentativeColourSurvives G (fun u=>(σ u).1) v

def coinRetainedColour {V C : Type*} (G : SimpleGraph V)
    (σ : V → C×Bool) (v : V) : Option C :=
  if coinColourSurvives G σ v then some (σ v).1 else none

theorem coinRetainedColour_eq_some {V C : Type*} (G : SimpleGraph V)
    (σ : V → C×Bool) (v : V) (c : C) :
    coinRetainedColour G σ v=some c ↔ (σ v).1=c ∧ coinColourSurvives G σ v := by
  unfold coinRetainedColour
  split_ifs <;> simp_all

theorem coinRetainedColour_proper {V C : Type*} (G : SimpleGraph V)
    (σ : V → C×Bool) {u v : V} (h : G.Adj u v) (c : C)
    (hu : coinRetainedColour G σ u=some c) : coinRetainedColour G σ v≠some c := by
  intro hv
  obtain ⟨huc,_,hus⟩ := (coinRetainedColour_eq_some G σ u c).mp hu
  obtain ⟨hvc,_⟩ := (coinRetainedColour_eq_some G σ v c).mp hv
  exact hus v h (hvc.trans huc.symm)

theorem coinRetainedColour_probability
    {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]
    (G : SimpleGraph V) (μ : V → FiniteLaw C)
    (a : V → C → ℝ) (ha : ∀ v c,0≤a v c ∧ a v c≤1) (v : V) (c : C) :
    (FiniteLaw.pi (fun u=>(μ u).withCoin (a u) (ha u))).probability
      (fun σ=>coinRetainedColour G σ v=some c)=
      (μ v).mass c*a v c*
        ∏ u∈Finset.univ.filter (fun u=>G.Adj v u),(1-(μ u).mass c) := by
  classical
  let ν := fun u=>(μ u).withCoin (a u) (ha u)
  let A : V → C×Bool → Prop := fun u x=>
    if u=v then x.1=c ∧ x.2=true else if G.Adj v u then x.1≠c else True
  have hevent (σ : V → C×Bool) :
      (coinRetainedColour G σ v=some c) ↔ ∀ u,A u (σ u) := by
    rw [coinRetainedColour_eq_some]
    constructor
    · rintro ⟨hc,hcoin,hkeep⟩ u
      by_cases hu : u=v
      · simp [A,hu,hc,hcoin]
      · by_cases hadj : G.Adj v u
        · simpa [A,hu,hadj,hc] using hkeep u hadj
        · simp [A,hu,hadj]
    · intro h
      obtain ⟨hc,hcoin⟩ : (σ v).1=c ∧ (σ v).2=true := by simpa [A] using h v
      refine ⟨hc,hcoin,?_⟩
      intro u hadj
      have huv : u≠v := fun he=>G.irrefl (he ▸ hadj)
      simpa [A,huv,hadj,hc] using h u
  rw [finiteLaw_probability_congr (FiniteLaw.pi ν) _ _ hevent,
    finiteLaw_pi_probability_forall ν A]
  have hcoord (u : V) : (ν u).probability (A u)=
      if u=v then (μ v).mass c*a v c else if G.Adj v u then 1-(μ u).mass c else 1 := by
    by_cases hu : u=v
    · subst u
      simp only [A,ite_true]
      exact finiteLaw_withCoin_success _ _ _ _
    · by_cases hadj : G.Adj v u
      · simp only [A,hu,ite_false,hadj,ite_true]
        exact finiteLaw_withCoin_not_colour _ _ _ _
      · simp only [A,hu,ite_false,hadj]
        exact finiteLaw_probability_true _
  simp_rw [hcoord]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun u=>if u=v then (μ v).mass c*a v c else if G.Adj v u then 1-(μ u).mass c else 1)
    (Finset.mem_univ v)]
  simp only [ite_true]
  congr 1
  have he : (Finset.univ.erase v).filter (fun u=>G.Adj v u)=
      Finset.univ.filter (fun u=>G.Adj v u) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_erase,Finset.mem_univ,and_true,true_and]
    constructor
    · exact fun h=>h.2
    · intro h
      exact ⟨fun he=>G.irrefl (he ▸ h),h⟩
  calc
    _ = ∏ u∈Finset.univ.erase v,if G.Adj v u then 1-(μ u).mass c else 1 := by
      apply Finset.prod_congr rfl
      intro u hu
      simp only [(Finset.mem_erase.mp hu).1,ite_false]
    _ = ∏ u∈(Finset.univ.erase v).filter (fun u=>G.Adj v u),(1-(μ u).mass c) := by
      rw [Finset.prod_filter]
    _ = _ := by rw [he]

end Oberwolfach
