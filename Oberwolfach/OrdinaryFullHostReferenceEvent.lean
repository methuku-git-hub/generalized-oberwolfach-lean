module

public import Oberwolfach.RawOrdinaryIsolatorProbability
public import Oberwolfach.RawOrdinaryTransferProbability
public import Oberwolfach.RawOrdinaryDegreeProbability
public import Oberwolfach.OrdinaryFullHostLoadProbability
public import Oberwolfach.FourCommonEvents

@[expose] public section

/-! The ordinary full-host reference event, for supplied fixed parent cycle
weights. All four conclusions hold on one event under the original raw law.
The configuration constants precede the error tolerance and interval length. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_full_host_reference_event
    (r : ℕ) (hr : 3≤r) (θ α pstar ω c B : ℝ)
    (hθ : (if r=3 then (3/4:ℝ) else 1/2)≤θ)
    (hα : 0<α) (hα1 : α≤1) (hθ1 : θ+α/2≤1)
    (hpstar : 0<pstar) (hpstar1 : pstar≤1) (hω : 0<ω) (hc : 0<c) (hB : 0<B) :
    ∃ k : ℕ,r+2≤k ∧ ∃ β : ℝ,0<β ∧ ∀ η : ℝ,0<η →
    ∃ ε₀ : ℝ,0<ε₀ ∧ ∀ L : ℝ,0≤L → ∀ d q₀ : ℕ,∀ hd : 2≤d,∃ N : ℕ,
    ∀ (V U Γ Color : Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],N≤Fintype.card V →
      ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ (P F : SimpleGraph V) (π : Equiv.Perm V),
      (∀ v,(θ+α)*Fintype.card V≤(P.degree v:ℝ)) →
      (∀ v,(F.degree v:ℝ)≤L) → permutationConflictGraph π (3*d)≤F →
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ pR pH D₀ ε : ℝ,∀ hRlo : pstar≤pR,∀ hRhi : pR≤1,pstar≤pH → pH≤1 →
      (Fintype.card V:ℝ)/2≤D₀ → 0≤ε → ε≤ε₀ →
      (∀ v,|(P.degree v:ℝ)-D₀|≤ε*Fintype.card V) → pR*D₀=2*(Fintype.card U:ℝ)*pH →
    ∀ (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j : Color),(∀ u,s u j=pH) →
    ∀ weight : OrdinaryCycle P r → ℝ,
      (∀ C,c/(Fintype.card V:ℝ)^(r-2)≤weight C ∧ weight C≤B/(Fintype.card V:ℝ)^(r-2)) →
      (∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0) →
    let μ := rawWheelLaw (fun _ : Sym2 V=>pR) (fun _=>(hpstar.trans_le hRlo).le) (fun _=>hRhi)
      d hd q hq hQ s hs hS
    let w := ordinaryFullHostSeed (U:=U) P F r weight pR pH
    (∀ W,c/(Fintype.card V:ℝ)^(r-1)≤w W ∧ w W≤
      (B/(ω*pstar^(2*r-1)))/(Fintype.card V:ℝ)^(r-1)) ∧
    1-1/(Fintype.card V:ℝ)^q₀≤(FiniteLaw.pi μ).probability (fun σ=>
      (∀ v : V,β*Fintype.card V≤(Fintype.card {u : U // rawWheelSpokes π d σ j v u}:ℝ)) ∧
      ((∀ x y,P.Adj x y → ¬F.Adj x y →
        |ordinaryPotentialLoad w (Sum.inl s(x,y)) ((rawWheelGraph P σ)\F) (rawWheelSpokes π d σ j)-1|≤η) ∧
       (∀ v u,|ordinaryPotentialLoad w (Sum.inr (v,u)) ((rawWheelGraph P σ)\F) (rawWheelSpokes π d σ j)-1|≤η)) ∧
      (∀ x y : V,x≠y → ¬F.Adj x y →
        β≤ordinaryIsolatorPotential P F (rawWheelSpokes π d σ j) k θ (α/4) x y (fun e=>σ (Sum.inl e))) ∧
      (∀ v : V,∀ u u' : U,u≠u' →β≤transferSurvivalSum r hr P F
        (transferRootCompletedSpokes (rawWheelSpokes π d σ j) v) v u u' (fun e=>σ (Sum.inl e)))) := by
  have hθ0 : 0≤θ := by
    have hh : (0:ℝ)≤ if r=3 then 3/4 else 1/2 := by split_ifs <;> norm_num
    exact hh.trans hθ
  obtain ⟨K,hK,hI⟩ := raw_ordinary_isolator_uniform_probability α pstar ω hα hα1 hpstar hpstar1 hω
  let k₀ := max K r
  obtain ⟨bI,hbI,hI⟩ := hI k₀ (le_max_left _ _)
  obtain ⟨bT,hbT,hT⟩ := raw_ordinary_transfer_uniform_probability r hr α pstar hα hpstar hpstar1 (by linarith only [hθ,hθ1])
  let β := min (pstar*ω/2) (min bI bT)
  have hβ : 0<β := lt_min (by positivity) (lt_min hbI hbT)
  have hβD : β≤pstar*ω/2 := min_le_left _ _
  have hβI : β≤bI := (min_le_right _ _).trans (min_le_left _ _)
  have hβT : β≤bT := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨2+k₀,by dsimp [k₀];omega,β,hβ,?_⟩
  intro η hη
  obtain ⟨ε₀,hε₀,hload⟩ := ordinaryFullHostSeed_uniform_probability r hr pstar ω c B η hpstar hω hc.le hB hη
  refine ⟨ε₀,hε₀,?_⟩
  intro L hL d q₀ hd
  obtain ⟨N₁,h₁⟩ := rawWheelSpokeDegrees_uniform_probability pstar ω hpstar hω d (q₀+1) hd
  obtain ⟨N₂,h₂⟩ := hload L hL d (q₀+1) hd
  obtain ⟨N₃,h₃⟩ := hI L hL d (q₀+1) hd
  obtain ⟨N₄,h₄⟩ := hT L hL d (q₀+1) hd
  refine ⟨max 4 (max N₁ (max N₂ (max N₃ N₄))),?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN hmlo hmhi P F π hP hF hclose hnoshort
    pR pH D₀ ε hRlo hRhi hHlo hHhi hD hε hεsmall hdeg hbalance q hq hQ s hs hS j hj weight hw he μ w
  let n := Fintype.card V
  have hn : 0<n := by dsimp [n];omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hm0 : (0:ℝ)<Fintype.card U := (mul_pos hω hn0).trans_le hmlo
  have hm : 0<Fintype.card U := by exact_mod_cast hm0
  refine ⟨ordinaryFullHostSeed_bounds P F r (by omega) weight pR pH ω pstar c B hn hm
    hω hpstar hmlo hmhi hRlo hRhi hHlo hHhi hc.le hB.le hw,?_⟩
  have hdegree := h₁ V U Γ Color (by omega) hmlo hmhi π (fun _ : Sym2 V=>pR)
    (fun _=>(hpstar.trans_le hRlo).le) (fun _=>hRhi) q hq hQ s hs hS j hnoshort pH hHlo hj
  have hloads := h₂ V U Γ Color (by omega) hmlo hmhi P F π hF hclose hnoshort
    pR pH D₀ ε hRlo hRhi hHlo hHhi hD hε hεsmall hdeg hbalance q hq hQ s hs hS j hj weight hw he
  have hisolator := h₃ V U Γ Color (by omega) hmlo hmhi P F π θ hθ0 hθ1 hP hF hclose
    (fun _ : Sym2 V=>pR) (fun _=>(hpstar.trans_le hRlo).le) (fun _=>hRhi) (fun _ _=>hRlo)
    q hq hQ s hs hS j hnoshort pH hHlo hj
  have htransfer := h₄ V U Γ Color (by omega) hmhi P F π
    (fun v=>(mul_le_mul_of_nonneg_right (add_le_add hθ (le_refl α)) hn0.le).trans (hP v)) hF
    (fun _ : Sym2 V=>pR) (fun _=>(hpstar.trans_le hRlo).le) (fun _=>hRhi) (fun _ _=>hRlo)
    q hq hQ s hs hS j hnoshort pH hHlo hj
  have hjoint := finiteLaw_four_events_lower (FiniteLaw.pi μ) _ _ _ _ (1/(n:ℝ)^(q₀+1)) hdegree hloads hisolator htransfer
  have hsum := scaled_inverse_power_le n q₀ hn 4 (by exact_mod_cast (show 4≤n by dsimp [n];omega))
  have hbound : 1-1/(n:ℝ)^q₀≤1-4*(1/(n:ℝ)^(q₀+1)) := by
    convert sub_le_sub_left hsum 1 using 1 <;> ring
  apply (hbound.trans hjoint).trans
  apply finiteLaw_probability_mono
  intro σ hσ
  refine ⟨?_,hσ.2.1,?_,?_⟩
  · intro v
    exact (mul_le_mul_of_nonneg_right hβD hn0.le).trans (hσ.1 v)
  · intro x y hxy hfxy
    exact hβI.trans (hσ.2.2.1 x y hxy hfxy)
  · intro v u u' huu
    exact hβT.trans (hσ.2.2.2 v u u' huu)

end Oberwolfach
