module

public import Oberwolfach.FiniteProductRegrouping
public import Oberwolfach.RandomColourCuts

@[expose] public section

/-! The five physical states in the marked sample: absent, or a directed
ordinary or marked edge. The representation by three colours and a fair
direction is proved equal to this law, including the combined absent mass. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def markedPhysicalProbability (p k : ℝ) : Fin 3→ℝ := ![2*p,2*k,1-2*p-2*k]

theorem markedPhysicalProbability_nonneg (p k : ℝ) (hp : 0≤p) (hk : 0≤k)
    (hsum : 2*p+2*k≤1) (a : Fin 3) : 0≤markedPhysicalProbability p k a := by
  fin_cases a <;> simp [markedPhysicalProbability] <;> linarith

theorem markedPhysicalProbability_sum (p k : ℝ) : ∑ a,markedPhysicalProbability p k a=1 := by
  simp [Fin.sum_univ_succ,markedPhysicalProbability]

def markedPhysicalLaw (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1) :
    FiniteLaw (Option (Bool×Bool)) where
  mass z := match z with
    | none=>1-2*p-2*k
    | some (b,_)=>if b then k else p
  nonneg z := by cases z with
    | none=>linarith
    | some z=>rcases z with ⟨b,c⟩;cases b <;> assumption
  total := by
    simp only [Fintype.sum_option,Fintype.sum_prod_type,Fintype.sum_bool,Bool.false_eq_true,↓reduceIte]
    ring

def markedPhysicalCollapse (z : Fin 3×Bool) : Option (Bool×Bool) :=
  if z.1=0 then some (false,z.2) else if z.1=1 then some (true,z.2) else none

theorem markedPhysicalCollapse_law (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1) :
    (FiniteLaw.categoricalDirection (markedPhysicalProbability p k)
      (markedPhysicalProbability_nonneg p k hp hk hsum) (markedPhysicalProbability_sum p k)).map
        markedPhysicalCollapse=markedPhysicalLaw p k hp hk hsum := by
  apply finiteLaw_ext
  intro z
  cases z with
  | none=>
    simp [FiniteLaw.map,FiniteLaw.categoricalDirection,markedPhysicalProbability,
      markedPhysicalCollapse,markedPhysicalLaw,Fintype.sum_prod_type,Fin.sum_univ_succ,Fintype.sum_bool]
  | some z=>
    rcases z with ⟨b,c⟩
    cases b <;> cases c <;>
      simp [FiniteLaw.map,FiniteLaw.categoricalDirection,markedPhysicalProbability,
        markedPhysicalCollapse,markedPhysicalLaw,Fintype.sum_prod_type,Fin.sum_univ_succ,Fintype.sum_bool]

def markedPhysicalOrientation {V : Type*} [LinearOrder V]
    (P : SimpleGraph V) (π : Equiv.Perm V) (σ : Sym2 V→Option (Bool×Bool))
    (b : Bool) (x y : V) : ℕ :=
  let z := if b then π y else y
  if P.Adj x z ∧ σ s(x,z)=some (b,orientationBit x z) then 1 else 0

theorem markedPhysicalCollapse_orientation {V : Type*} [LinearOrder V]
    (P : SimpleGraph V) (π : Equiv.Perm V) (σ : Sym2 V→Fin 3×Bool) (b : Bool) (x y : V) :
    markedPhysicalOrientation P π (fun e=>markedPhysicalCollapse (σ e)) b x y=
      sampledColourOrientation P σ (if b then 1 else 0) x (if b then π y else y) := by
  cases b <;> unfold markedPhysicalOrientation sampledColourOrientation markedPhysicalCollapse <;>
    simp only [Bool.false_eq_true,↓reduceIte] <;>
    split_ifs <;> simp_all [Prod.ext_iff]

/-- This is an equality of laws for arbitrary events, not only a marginal
edge estimate. It can therefore be used before later adaptive choices. -/
theorem markedPhysical_orientation_probability
    {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V) (π : Equiv.Perm V)
    (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1)
    (E : (Bool→V→V→ℕ)→Prop) :
    (FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)).probability
      (fun σ=>E (markedPhysicalOrientation P π σ))=
    (FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.categoricalDirection (markedPhysicalProbability p k)
      (markedPhysicalProbability_nonneg p k hp hk hsum) (markedPhysicalProbability_sum p k))).probability
      (fun σ=>E (fun b x y=>sampledColourOrientation P σ (if b then 1 else 0) x (if b then π y else y))) := by
  have hh := finiteLaw_map_probability
    (FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.categoricalDirection (markedPhysicalProbability p k)
      (markedPhysicalProbability_nonneg p k hp hk hsum) (markedPhysicalProbability_sum p k)))
    (fun σ e=>markedPhysicalCollapse (σ e)) (fun σ=>E (markedPhysicalOrientation P π σ))
  rw [finiteLaw_pi_map] at hh
  rw [markedPhysicalCollapse_law p k hp hk hsum] at hh
  rw [hh]
  congr 1
  funext σ
  congr 1
  funext b x y
  exact markedPhysicalCollapse_orientation P π σ b x y

end Oberwolfach
