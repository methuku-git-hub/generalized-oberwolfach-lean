module

public import Oberwolfach.RawSelectedSpokeCuts
public import Oberwolfach.RawMarkedHubCounts

@[expose] public section

/-! Both spoke types satisfy large cuts on the original interval sample.
The selected interval and ordinary colours are kept in their original
joint law; their mutual exclusion is not replaced by independence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rawMarked_spoke_cuts
    (tstar ω : ℝ) (htstar : 0<tstar) (htstar1 : tstar≤1) (hω : 0<ω)
    (d q₀ : ℕ) (hd : 2≤d) :
    ∃ N : ℕ,∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ (π : Equiv.Perm V)
      (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (g : Γ) (j : Color) (s₀ t₀ : ℝ),(∀ u,q u g=t₀) → (∀ u,s u j=s₀) → tstar≤s₀ → tstar≤t₀ →
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    1-1/(Fintype.card V:ℝ)^q₀≤
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ b : Bool,∀ (X : Finset V) (Y : Finset U),
          1-tstar/8<(X.card:ℝ)/Fintype.card V+(Y.card:ℝ)/Fintype.card U →
          tstar/8*min ((Fintype.card U:ℝ)*X.card) ((Fintype.card V:ℝ)*Y.card)≤
            (bipartiteMatrixCut (fun v u=>if rawMarkedSpokes π d σ g j b v u then 1 else 0) X Y:ℝ)) := by
  obtain ⟨N,hN⟩ := rawSelectedSpokeMatrix_large_cuts tstar ω htstar htstar1 hω d (q₀+1) hd
  refine ⟨max 2 N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN hmlo hmhi π q hq hQ s hs hS g j s₀ t₀ hg hj hslo htlo hnoshort
  let n := Fintype.card V
  have hn : 0<n := by dsimp [n];omega
  let μ := FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  let E := fun (b : Bool) (σ : RawIntervalFamilyOutcome V U Γ Color)=>∀ (X : Finset V) (Y : Finset U),
    1-tstar/8<(X.card:ℝ)/Fintype.card V+(Y.card:ℝ)/Fintype.card U →
    tstar/8*min ((Fintype.card U:ℝ)*X.card) ((Fintype.card V:ℝ)*Y.card)≤
      (bipartiteMatrixCut (fun v u=>if rawMarkedSpokes π d σ g j b v u then 1 else 0) X Y:ℝ)
  have hevent (b : Bool) : 1-1/(n:ℝ)^(q₀+1)≤μ.probability (E b) := by
    have hmarg (u : U) : Sum.elim (q u) (s u) (if b then Sum.inl g else Sum.inr j)=
        if b then t₀ else s₀ := by
      cases b
      · exact hj u
      · exact hg u
    have hlo : tstar≤(if b then t₀ else s₀) := by cases b <;> assumption
    have hh := hN V U Γ Color (by omega) hmlo hmhi π q hq hQ s hs hS
      (if b then Sum.inl g else Sum.inr j) hnoshort (if b then t₀ else s₀) hlo hmarg
    have hmatrix (σ : RawIntervalFamilyOutcome V U Γ Color) :
        (fun v u=>if rawMarkedSpokes π d σ g j b v u then (1:ℕ) else 0)=
          rawSelectedSpokeMatrix π d σ (if b then Sum.inl g else Sum.inr j) := by
      funext v u
      cases b <;> unfold rawMarkedSpokes rawSelectedSpokeMatrix <;>
        simp only [Bool.false_eq_true,↓reduceIte] <;> split_ifs <;> rfl
    apply hh.trans
    apply finiteLaw_probability_mono
    intro σ hσ X Y hlarge
    rw [hmatrix σ]
    exact hσ X Y hlarge
  have hjoint := finiteLaw_good_intersection μ (E false) (E true) (1/(n:ℝ)^(q₀+1)) (hevent true)
  have hbase := (sub_le_sub_right (hevent false) (1/(n:ℝ)^(q₀+1))).trans hjoint
  have hsum := scaled_inverse_power_le n q₀ hn 2 (by exact_mod_cast (show 2≤n by dsimp [n];omega))
  have hbound : 1-1/(n:ℝ)^q₀≤(1-1/(n:ℝ)^(q₀+1))-1/(n:ℝ)^(q₀+1) := by
    convert sub_le_sub_left hsum 1 using 1 <;> ring
  apply (hbound.trans hbase).trans
  apply finiteLaw_probability_mono
  intro σ hσ b
  cases b
  · exact hσ.1
  · exact hσ.2

end Oberwolfach
