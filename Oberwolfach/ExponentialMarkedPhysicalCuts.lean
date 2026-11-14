module

public import Oberwolfach.MarkedPhysicalLaw
public import Oberwolfach.ExponentialSeparatedColourCuts
public import Oberwolfach.MarkedPhysicalCuts

@[expose] public section

/-! Large cuts for the two actual marked physical arc types, with the
source coefficient αp/4 (respectively αk/4). Both types use the same
five-state experiment on unordered physical edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem markedPhysical_large_cuts_exponential
    (α pstar : ℝ) (hα : 0<α) (hα1 : α≤1/2) (hpstar : 0<pstar)
    (b : ℕ) :
    ∃ N : ℕ,1≤N ∧ ∀ (V : Type) [Fintype V] [LinearOrder V],N≤Fintype.card V →
    ∀ (P : SimpleGraph V),(∀ v,(1/2+α)*Fintype.card V≤(P.degree v:ℝ)) →
    ∀ (π : Equiv.Perm V) (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1),
      pstar≤p → pstar≤k →
    1-24*Fintype.card V*Real.exp
      (-min (2*(2*pstar/32)^2) ((α*(2*pstar)^2/1024)^2/4)*Fintype.card V)≤
      (FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)).probability
        (fun σ=>∀ a : Bool,∀ δ : ℝ,δ≤α/32 → δ≤(if a then k else p)/32 → ∀ S T : Finset V,
          (1-2*δ)*Fintype.card V<(S.card:ℝ)+T.card →
          (α*(if a then k else p)/4)*Fintype.card V*min (S.card:ℝ) T.card≤
            (matrixCut (markedPhysicalRim P π b σ a) S T:ℝ)) := by
  obtain ⟨N,hN1,hN⟩ := sampledColourOrientation_separated_large_cuts_exponential α (2*pstar) hα hα1
    (by positivity) 3 b
  refine ⟨N,hN1,?_⟩
  intro V _ _ hn P hP π p k hp hk hsum hlo klo
  unfold markedPhysicalRim
  rw [markedPhysical_orientation_probability P π p k hp hk hsum
    (fun R=>∀ a : Bool,∀ δ : ℝ,δ≤α/32 → δ≤(if a then k else p)/32 → ∀ S T : Finset V,
      (1-2*δ)*Fintype.card V<(S.card:ℝ)+T.card →
      (α*(if a then k else p)/4)*Fintype.card V*min (S.card:ℝ) T.card≤
        (matrixCut (permutationSeparatedMatrix π b (R a)) S T:ℝ))]
  have hh := hN V hn P hP (markedPhysicalProbability p k)
    (markedPhysicalProbability_nonneg p k hp hk hsum) (markedPhysicalProbability_sum p k)
  norm_num only [Nat.cast_ofNat,show (8:ℝ)*3=24 by norm_num] at hh
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ a δ hδα hδa S T hlarge
  have ha : markedPhysicalProbability p k (if a then 1 else 0)=2*(if a then k else p) := by
    cases a <;> simp [markedPhysicalProbability]
  have hlo' : 2*pstar≤markedPhysicalProbability p k (if a then 1 else 0) := by
    rw [ha];cases a <;> simp only [Bool.false_eq_true,↓reduceIte] <;> linarith
  have hh := hσ (if a then 1 else 0) hlo' π (if a then π else Equiv.refl V) δ hδα
    (by rw [ha];linarith only [hδa]) S T hlarge
  rw [ha] at hh
  have he : (fun x y=>sampledColourOrientation P σ (if a then 1 else 0) x
      ((if a then π else Equiv.refl V) y))=
    (fun x y=>sampledColourOrientation P σ (if a then 1 else 0) x (if a then π y else y)) := by
      funext x y;cases a <;> rfl
  rw [he] at hh
  convert hh using 1 <;> ring

end Oberwolfach
