module

public import Oberwolfach.RawMarkedNeighbourhoodEvents

@[expose] public section

/-! Explicit exponential errors for the marked spoke neighbourhoods.
Distinct hub tuples are all tested on one original raw interval sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

theorem rawMarkedNeighbourhood_exponential_event
    (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (hn : 0<Fintype.card V) (g : Γ) (j : Color) (s₀ t₀ : ℝ)
    (hg : ∀ u,q u g=t₀) (hj : ∀ u,s u j=s₀)
    (k : ℕ) (hk : 0<k) (t : ℝ) (ht : 0<t) :
    1-4*(Fintype.card U:ℝ)^k*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((k:ℝ)*Fintype.card V)))≤
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀ (b : Bool) (u : Fin k→U),Function.Injective u →
        |((Finset.univ.filter (fun v=>∀ i,rawMarkedSpokes π d σ g j b v (u i))).card:ℝ)-
          (if b then t₀ else s₀)^k*Fintype.card V|<t) := by
  let I := Bool×(Fin k→U)
  let J (i : I) := Finset.univ.image i.2
  let col (i : I) (_ : U) : Γ⊕Color := if i.1 then Sum.inl g else Sum.inr j
  have hJ (i : I) : (J i).Nonempty :=
    ⟨i.2 ⟨0,hk⟩,Finset.mem_image.mpr ⟨⟨0,hk⟩,Finset.mem_univ _,rfl⟩⟩
  have hsize (i : I) : (J i).card≤k := Finset.card_image_le.trans (by simp)
  have hh := rawIntervalSelectedNeighbourCount_common_event π d hd q hq hQ s hs hS hnoshort hn
    col (fun _=>Finset.univ) J hJ k hk hsize t ht
  have hcard : (Fintype.card I:ℝ)=2*(Fintype.card U:ℝ)^k := by simp [I]
  rw [hcard] at hh
  simp only [Finset.card_univ] at hh
  have hh' : 1-4*(Fintype.card U:ℝ)^k*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((k:ℝ)*Fintype.card V)))≤
      (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ i : I,|rawIntervalSelectedNeighbourCount π d σ (col i) Finset.univ (J i)-
          (Fintype.card V:ℝ)*(∏ u∈J i,Sum.elim (q u) (s u) (col i u))|<t) := by
    convert hh using 1 <;> ring
  apply hh'.trans
  apply finiteLaw_probability_mono
  intro σ hσ b u hu
  have hcount := hσ (b,u)
  have hcardJ : (Finset.univ.image u).card=k := by rw [Finset.card_image_of_injective _ hu];simp
  have hprob (v : U) : Sum.elim (q v) (s v) (if b then Sum.inl g else Sum.inr j)=
      if b then t₀ else s₀ := by cases b <;> simp [hg,hj]
  simp only [col,J,hprob,Finset.prod_const,hcardJ,Finset.card_univ] at hcount
  have he := rawMarkedNeighbourhood_count π d σ g j b Finset.univ u
  simpa only [he,Finset.card_univ,mul_comm] using hcount

end Oberwolfach
