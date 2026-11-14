module

public import Oberwolfach.RawIntervalSelectedNeighbours
public import Oberwolfach.RawMarkedHubCounts
public import Oberwolfach.ConfigurationFailureMargins

@[expose] public section

/-! A common event for both marked spoke types, fixed distinct hub tuples,
and all ambient-root neighbourhoods. The inverse-image neighbourhood is
included explicitly; roots are not confined to an induced subgraph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

def markedReferenceDomain (P : SimpleGraph V) (π : Equiv.Perm V) : Option (V⊕V)→Finset V
  | none=>Finset.univ
  | some (Sum.inl x)=>P.neighborFinset x
  | some (Sum.inr x)=>Finset.univ.filter (fun v=>P.Adj x (π v))

theorem rawMarkedNeighbourhood_count
    (π : Equiv.Perm V) (d : ℕ) (σ : RawIntervalFamilyOutcome V U Γ Color)
    (g : Γ) (j : Color) (b : Bool) (A : Finset V) {k : ℕ} (u : Fin k→U) :
    ((A.filter (fun v=>∀ i,rawMarkedSpokes π d σ g j b v (u i))).card:ℝ)=
      rawIntervalSelectedNeighbourCount π d σ (fun _=>if b then Sum.inl g else Sum.inr j)
        A (Finset.univ.image u) := by
  rw [Finset.card_filter,Nat.cast_sum]
  simp only [rawIntervalSelectedNeighbourCount,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro v _
  cases b <;> simp [rawMarkedSpokes]

theorem rawMarkedNeighbourhood_uniform_event
    (ε : ℝ) (hε : 0<ε) (k d q₀ : ℕ) (hk : 0<k) (hd : 2≤d) :
    ∃ N : ℕ,∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V → Fintype.card U≤Fintype.card V →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V)
      (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (g : Γ) (j : Color) (s₀ t₀ : ℝ),(∀ u,q u g=t₀) → (∀ u,s u j=s₀) →
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    1-1/(Fintype.card V:ℝ)^q₀≤
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ (b : Bool) (u : Fin k→U),Function.Injective u → ∀ z : Option (V⊕V),
          |(((markedReferenceDomain P π z).filter
            (fun v=>∀ i,rawMarkedSpokes π d σ g j b v (u i))).card:ℝ)-
            (if b then t₀ else s₀)^k*(markedReferenceDomain P π z).card|<ε*Fintype.card V) := by
  have hk0 : (0:ℝ)<k := by exact_mod_cast hk
  obtain ⟨N,hN⟩ := linear_deviation_failure_eventually_small 6 ((4*(d:ℝ)+3)^2*k)
    ε (by positivity) hε (k+1) q₀
  refine ⟨max N 1,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN hmhi P π q hq hQ s hs hS g j s₀ t₀ hg hj hnoshort
  let n := Fintype.card V
  have hn : 0<n := by dsimp [n];omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  let I := Bool×(Fin k→U)×Option (V⊕V)
  let A (i : I) := markedReferenceDomain P π i.2.2
  let J (i : I) := Finset.univ.image i.2.1
  let col (i : I) (_ : U) : Γ⊕Color := if i.1 then Sum.inl g else Sum.inr j
  have hJ (i : I) : (J i).Nonempty :=
    ⟨i.2.1 ⟨0,hk⟩,Finset.mem_image.mpr ⟨⟨0,hk⟩,Finset.mem_univ _,rfl⟩⟩
  have hsize (i : I) : (J i).card≤k := (Finset.card_image_le).trans (by simp)
  have hh := rawIntervalSelectedNeighbourCount_common_event π d hd q hq hQ s hs hS hnoshort hn
    col A J hJ k hk hsize (ε*n) (by positivity)
  have hcard : Fintype.card I≤6*n^(k+1) := by
    simp only [I,Fintype.card_prod,Fintype.card_bool,Fintype.card_fun,Fintype.card_fin,
      Fintype.card_option,Fintype.card_sum]
    calc
      2*((Fintype.card U)^k*(Fintype.card V+Fintype.card V+1))≤2*(n^k*(3*n)) := by
        gcongr
        dsimp [n]
        omega
      _=6*n^(k+1) := by rw [pow_succ];ring
  have hcardR : (Fintype.card I:ℝ)≤6*(n:ℝ)^(k+1) := by exact_mod_cast hcard
  have ht := hN n (by dsimp [n] at *;omega) (Fintype.card I)
    ((4*(d:ℝ)+3)^2*((k:ℝ)*n)) (by positivity) hcardR (by positivity)
    (by exact le_of_eq (by ring))
  apply ((sub_le_sub_left ht 1).trans hh).trans
  apply finiteLaw_probability_mono
  intro σ hσ b u hu z
  have hcount := hσ (b,u,z)
  have hcardJ : (Finset.univ.image u).card=k := by rw [Finset.card_image_of_injective _ hu];simp
  have hprob (v : U) : Sum.elim (q v) (s v) (if b then Sum.inl g else Sum.inr j)=
      if b then t₀ else s₀ := by cases b <;> simp [hg,hj]
  simp only [col,A,J,hprob,Finset.prod_const,hcardJ] at hcount
  rw [rawMarkedNeighbourhood_count]
  convert hcount using 1 <;> ring

end Oberwolfach
