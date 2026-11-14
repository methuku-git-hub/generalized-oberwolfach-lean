module

public import Oberwolfach.RawIntervalSelectedNeighbours
public import Oberwolfach.RawMarkedHubCounts
public import Oberwolfach.PermutationNeighbourCounts
public import Oberwolfach.ExponentialConfigurationMargins

@[expose] public section

/-! One-hub counts on a fixed inner domain with every ambient vertex
allowed as a root. The ambient size is bounded by K times the inner order;
no assertion about external roots is inferred from an induced graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def markedLocalDomain (P : SimpleGraph V) (π : Equiv.Perm V) (A : Finset V) : Option (V⊕V)→Finset V
  | none=>A
  | some (Sum.inl x)=>P.neighborFinset x∩A
  | some (Sum.inr x)=>A.filter (fun v=>P.Adj x (π v))

def rawMarkedLocalClass (π : Equiv.Perm V) (d : ℕ) (σ : RawIntervalFamilyOutcome V U Γ Color)
    (g : Γ) (j : Color) (A : Finset V) (b : Bool) (u : U) : Finset V :=
  A.filter (fun v=>rawMarkedSpokes π d σ g j b v u)

theorem rawMarkedLocal_domain_event (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (P : SimpleGraph V) (A : Finset V) (hA : A.Nonempty) (K ε : ℝ) (hK : 1≤K) (hε : 0<ε)
    (hV : (Fintype.card V:ℝ)≤K*A.card) (hU : (Fintype.card U:ℝ)≤K*A.card)
    (g : Γ) (j : Color) (s₀ t₀ : ℝ) (hg : ∀ u,q u g=t₀) (hj : ∀ u,s u j=s₀) :
    1-12*K^2*(A.card:ℝ)^2*Real.exp (-(2*ε^2/((4*(d:ℝ)+3)^2*K))*A.card)≤
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ (b : Bool) (u : U) (z : Option (V⊕V)),
          |(((markedLocalDomain P π A z).filter (fun v=>rawMarkedSpokes π d σ g j b v u)).card:ℝ)-
            (if b then t₀ else s₀)*(markedLocalDomain P π A z).card|<ε*A.card) := by
  let I := Bool×U×Option (V⊕V)
  let col := fun (i : I) (_ : U)=>if i.1 then Sum.inl g else Sum.inr j
  have hn : 0<Fintype.card V := hA.card_pos.trans_le A.card_le_univ
  have hnR : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have haR : (0:ℝ)<A.card := by exact_mod_cast hA.card_pos
  have hh := rawIntervalSelectedNeighbourCount_common_event π d hd q hq hQ s hs hS hnoshort hn
    col (fun i=>markedLocalDomain P π A i.2.2) (fun i=>{i.2.1})
    (fun i=>Finset.singleton_nonempty _) 1 (by omega) (by intro i;simp) (ε*A.card) (by positivity)
  have hcard : (Fintype.card I:ℝ)≤6*K^2*(A.card:ℝ)^2 := by
    have hn1 : (1:ℝ)≤Fintype.card V := by exact_mod_cast hn
    simp only [I,Fintype.card_prod,Fintype.card_bool,Fintype.card_option,Fintype.card_sum,Nat.cast_mul,
      Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
    calc
      2*((Fintype.card U:ℝ)*(Fintype.card V+Fintype.card V+1))≤2*((K*A.card)*(3*(K*A.card))) := by
        gcongr
        linarith
      _ = _ := by ring
  have ht := linear_deviation_failure_exponential (6*K^2) ((4*(d:ℝ)+3)^2*K) ε
    (by positivity) hε 2 A.card hA.card_pos (Fintype.card I) ((4*(d:ℝ)+3)^2*Fintype.card V)
    (by positivity) hcard (by positivity) (by nlinarith only [mul_le_mul_of_nonneg_left hV (sq_nonneg (4*(d:ℝ)+3))])
  simp only [Nat.cast_one,one_mul] at hh
  have hprob := (sub_le_sub_left ht 1).trans hh
  have he : 2*(6*K^2)=12*K^2 := by ring
  rw [he] at hprob
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro σ hσ b u z
  have hi := hσ (b,u,z)
  have hp : Sum.elim (q u) (s u) (if b then Sum.inl g else Sum.inr j)=if b then t₀ else s₀ := by
    cases b <;> simp [hg,hj]
  simp only [col,Finset.prod_singleton,hp] at hi
  have hcount : rawIntervalSelectedNeighbourCount π d σ (fun _=>if b then Sum.inl g else Sum.inr j)
      (markedLocalDomain P π A z) {u}=
      (((markedLocalDomain P π A z).filter (fun v=>rawMarkedSpokes π d σ g j b v u)).card:ℝ) := by
    simp only [rawIntervalSelectedNeighbourCount,Finset.mem_singleton,forall_eq,
      Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,rawMarkedSpokes]
    cases b <;> simp [Finset.card_filter, Nat.cast_sum, -Finset.sum_boole]
    all_goals
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs <;> rfl
  rw [hcount] at hi
  simpa only [mul_comm] using hi

end Oberwolfach
