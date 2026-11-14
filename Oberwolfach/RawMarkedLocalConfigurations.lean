module

public import Oberwolfach.MarkedLocalDenseClasses
public import Oberwolfach.MarkedLocalPhysicalEvent
public import Oberwolfach.RawMarkedPotentialSampling
public import Oberwolfach.ProductGoodEvents
public import Oberwolfach.FiniteSumProduct

@[expose] public section

/-! Local marked cycle and path counts, with arbitrary ambient roots,
on the unchanged raw product law. The inner domain is fixed before exposure. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def markedLocalConfigurationExponent (r : ℕ) (α tstar kstar K : ℝ) (d : ℕ) : ℝ :=
  min (2*(min (tstar/4) (α*tstar/8))^2/((4*(d:ℝ)+3)^2*K))
    (markedLocalSurvivalExponent r α (tstar/2) kstar K)

theorem markedLocalConfigurationExponent_pos (r : ℕ) (α tstar kstar K : ℝ) (d : ℕ)
    (hα : 0<α) (htstar : 0<tstar) (hkstar : 0<kstar) (hK : 0<K) :
    0<markedLocalConfigurationExponent r α tstar kstar K d := by
  apply lt_min
  · positivity
  · exact markedLocalSurvivalExponent_pos r α (tstar/2) kstar K hα (by positivity) hkstar hK

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def RawMarkedLocalConfigurations (r : ℕ) (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ)
    (g : Γ) (j : Color) (A : Finset V) (βC βP : ℝ) (σ : RawMarkedOutcome V U Γ Color) : Prop :=
  MarkedLocalPhysicalCounts r (3*d) P π
    (fun u=>rawMarkedLocalClass π d (fun e=>σ (Sum.inr e)) g j A false u)
    (fun u=>rawMarkedLocalClass π d (fun e=>σ (Sum.inr e)) g j A true u)
    A.card βC βP (fun e=>σ (Sum.inl e))

theorem rawMarked_local_configurations_event
    (r : ℕ) (hr : 1≤r) (α tstar kstar K : ℝ) (hα : 0<α) (hα1 : α≤1/2)
    (htstar : 0<tstar) (hkstar : 0<kstar) (hK : 1≤K) (d : ℕ) (hd : 2≤d) :
    ∃ N : ℕ,∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V) (A : Finset V), N≤A.card →
      (∀ x,π x∈A ↔ x∈A) → (Fintype.card V:ℝ)≤K*A.card → (Fintype.card U:ℝ)≤K*A.card →
      (∀ x,(1/2+α)*A.card≤((P.neighborFinset x∩A).card:ℝ)) →
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1),kstar≤p → kstar≤k →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (g : Γ) (j : Color) (s₀ t₀ : ℝ),(∀ u,q u g=t₀) → (∀ u,s u j=s₀) → tstar≤s₀ → tstar≤t₀ →
    1-(12*K^2+2*K+4*K^3)*(A.card:ℝ)^3*
      Real.exp (-markedLocalConfigurationExponent r α tstar kstar K d*A.card)≤
    (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).probability
      (RawMarkedLocalConfigurations r P π d g j A
        (markedLocalCycleCoefficient r α (tstar/2) kstar) (markedLocalPathCoefficient r α (tstar/2) kstar)) := by
  have hK0 : 0<K := lt_of_lt_of_le (by norm_num) hK
  obtain ⟨N₂,hN₂⟩ := markedLocal_physical_event r (3*d) (by omega) hr α (tstar/2) kstar K
    hα (by linarith) (by positivity) hkstar hK0
  refine ⟨max 1 N₂,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P π A hAN hInv hV hU hP hnoshort p k hp hk hsum hpmin hkmin q hq hQ s hs hS g j s₀ t₀ hg hj hslo htlo
  have hA : A.Nonempty := Finset.card_pos.mp (by omega)
  have haR : (1:ℝ)≤A.card := by exact_mod_cast hA.card_pos
  let a := A.card
  let θ := tstar/2
  let T := fun (σ : RawIntervalFamilyOutcome V U Γ Color) u b=>rawMarkedLocalClass π d σ g j A b u
  let μ := FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  let ν := FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)
  let E := fun σ : RawIntervalFamilyOutcome V U Γ Color=>∀ u : U,
    Disjoint (T σ u false) (T σ u true) ∧ Disjoint (T σ u false) ((T σ u true).image π) ∧
      ∀ b : Bool,(θ*a≤((T σ u b).card:ℝ)) ∧
        (∀ x,(1/2+α/2)*(T σ u b).card≤((P.neighborFinset x∩T σ u b).card:ℝ)) ∧
        (∀ x,(1/2+α/2)*(T σ u b).card≤((P.neighborFinset x∩(T σ u b).image π).card:ℝ))
  let Good := fun σ τ=>MarkedLocalPhysicalCounts r (3*d) P π (fun u=>T σ u false) (fun u=>T σ u true) a
    (markedLocalCycleCoefficient r α θ kstar) (markedLocalPathCoefficient r α θ kstar) τ
  let cF := 2*(min (tstar/4) (α*tstar/8))^2/((4*(d:ℝ)+3)^2*K)
  let cS := markedLocalSurvivalExponent r α θ kstar K
  let errF := 12*K^2*(a:ℝ)^2*Real.exp (-cF*a)
  let errS := (2*K+4*K^3)*(a:ℝ)^3*Real.exp (-cS*a)
  have hfirst : 1-errF≤μ.probability E := rawMarkedLocal_dense_event π d hd q hq hQ s hs hS hnoshort P A hA hInv K α tstar hK hα hα1 htstar hV hU hP g j s₀ t₀ hg hj hslo htlo
  have hsecond (σ : RawIntervalFamilyOutcome V U Γ Color) (hσ : E σ) :
      1-errS≤ν.probability (Good σ) := by
    apply hN₂ V U a (by dsimp [a];omega) A.card_le_univ hV hU P π (fun u=>T σ u false) (fun u=>T σ u true)
    · intro u;exact (hσ u).2.2 false |>.1
    · intro u;exact (hσ u).2.2 true |>.1
    · intro u;exact (hσ u).2.2 false |>.2.1
    · intro u;exact (hσ u).2.2 true |>.2.1
    · intro u;exact (hσ u).2.2 true |>.2.2
    · exact hpmin
    · exact hkmin
  have hj := finiteLaw_product_good_lower μ ν E Good errF errS (by dsimp [errS];positivity) hfirst hsecond
  have hexF : Real.exp (-cF*a)≤Real.exp (-min cF cS*a) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left cF cS)) (Nat.cast_nonneg a))
  have hexS : Real.exp (-cS*a)≤Real.exp (-min cF cS*a) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right cF cS)) (Nat.cast_nonneg a))
  have ha23 : (a:ℝ)^2≤(a:ℝ)^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr haR) (sq_nonneg (a:ℝ))]
  have hsumerr : errF+errS≤(12*K^2+2*K+4*K^3)*(a:ℝ)^3*Real.exp (-min cF cS*a) := by
    calc
      errF+errS≤12*K^2*(a:ℝ)^3*Real.exp (-min cF cS*a)+(2*K+4*K^3)*(a:ℝ)^3*Real.exp (-min cF cS*a) := by
        dsimp [errF,errS]
        gcongr
      _ = _ := by ring
  have hbound : 1-(12*K^2+2*K+4*K^3)*(a:ℝ)^3*Real.exp (-min cF cS*a)≤1-errF-errS := by linarith only [hsumerr]
  have hprod : 1-(12*K^2+2*K+4*K^3)*(a:ℝ)^3*Real.exp (-min cF cS*a)≤
      (μ.prod ν).probability (fun z=>Good z.1 z.2) :=
    ((hbound.trans hj).trans (finiteLaw_probability_mono _ _ _ (fun z hz=>hz.2)))
  have heq := finiteLaw_pi_sum_probability (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS) Good
  change (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).probability
    (RawMarkedLocalConfigurations r P π d g j A (markedLocalCycleCoefficient r α θ kstar) (markedLocalPathCoefficient r α θ kstar))=
    (μ.prod ν).probability (fun z=>Good z.1 z.2) at heq
  rw [heq]
  exact hprod

end Oberwolfach
