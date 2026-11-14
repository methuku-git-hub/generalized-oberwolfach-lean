module

public import Oberwolfach.AllCutsExponentialMargins
public import Oberwolfach.ColourCutEvent

@[expose] public section

/-! A linear exponential failure bound for every quadratic physical-colour
cut test. Constants are uniform over the actual categorical probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sampledColourCut_quadratic_exponential_event (k : ℕ) {q : ℝ} (hq : 0<q) :
    ∃ N : ℕ,1≤N ∧ ∀ (V : Type) [Fintype V] [LinearOrder V],N≤Fintype.card V →
    ∀ (G : SimpleGraph V) (ρ : Fin k→ℝ) (hρ : ∀ a,0≤ρ a) (hsum : ∑ a,ρ a=1),
    1-2*k*Real.exp (-(q^2/4)*Fintype.card V)≤
    (FiniteLaw.pi (fun _ : Sym2 V=>FiniteLaw.categoricalDirection ρ hρ hsum)).probability
      (fun σ=>∀ a S T,
        |((∑ x∈S,∑ y∈T,sampledColourOrientation G σ a x y:ℕ):ℝ)-
          ρ a/2*graphCut G S T|<q*(Fintype.card V:ℝ)^2) := by
  obtain ⟨N,hN1,hN⟩ := eventually_allCuts_failure_exponential (c:=q^2/2) (by positivity)
  refine ⟨N,hN1,?_⟩
  intro V _ _ hn G ρ hρ hsum
  let n := Fintype.card V
  have hnpos : 0<n := by dsimp [n];omega
  have hnreal : (0:ℝ)<n := by exact_mod_cast hnpos
  have hh := sampledColourCut_all_cuts G hnpos ρ hρ hsum
    (fun _=>q*(n:ℝ)^2) (fun _=>by positivity)
  have heq : -(q*(n:ℝ)^2)^2/(2*(n:ℝ)^2)=-(q^2/2)*(n:ℝ)^2 := by
    field_simp
  change 1-(4:ℝ)^n*(∑ _a : Fin k,2*Real.exp (-(q*(n:ℝ)^2)^2/(2*(n:ℝ)^2)))≤_ at hh
  simp only [heq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  have hs := hN n hn (2*k) (by positivity)
  have heq' : (4:ℝ)^n*((k:ℝ)*(2*Real.exp (-(q^2/2)*(n:ℝ)^2)))=
      2*k*(4:ℝ)^n*Real.exp (-(q^2/2)*(n:ℝ)^2) := by ring
  rw [heq'] at hh
  have he : (q^2/2)/2=q^2/4 := by ring
  rw [he] at hs
  exact (sub_le_sub_left hs 1).trans hh

end Oberwolfach
