module

public import Oberwolfach.OrdinaryFullHostReferenceEvent
public import Oberwolfach.AlmostSpanningCyclePacking
public import Oberwolfach.OddSharpThreshold

@[expose] public section

/-! Parent cycle weights are chosen from the dense host before the hub set,
conflict graph, permutation, or sampling arrays. This discharges the fixed
coefficient input to the ordinary full-host reference event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_full_host_sampling_numerical
    (r : ℕ) (hr : 3≤r) (θ α pstar ω : ℝ)
    (hθ : cycleThreshold r≤θ) (hα : 0<α) (hα1 : α≤1) (hθ1 : θ+α/2≤1)
    (hpstar : 0<pstar) (hpstar1 : pstar≤1) (hω : 0<ω) :
    ∃ (k : ℕ) (β c B : ℝ),r+2≤k ∧ 0<β ∧ 0<c ∧ 0<B ∧ ∀ η : ℝ,0<η →
    ∃ ε₀ : ℝ,0<ε₀ ∧ ∀ L : ℝ,0≤L → ∀ d q₀ : ℕ,∀ hd : 2≤d,∃ N : ℕ,
    ∀ (V : Type) [Fintype V] [DecidableEq V],N≤Fintype.card V →
    ∀ P : SimpleGraph V,(∀ v,(θ+α)*Fintype.card V≤(P.degree v:ℝ)) →
    ∃ weight : OrdinaryCycle P r → ℝ,
      (∀ C,c/(Fintype.card V:ℝ)^(r-2)≤weight C ∧ weight C≤B/(Fintype.card V:ℝ)^(r-2)) ∧
      (∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0) ∧
    ∀ (U Γ Color : Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U],
      ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ (F : SimpleGraph V) (π : Equiv.Perm V),
      (∀ v,(F.degree v:ℝ)≤L) → permutationConflictGraph π (3*d)≤F →
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ pR pH D₀ ε : ℝ,∀ hRlo : pstar≤pR,∀ hRhi : pR≤1,pstar≤pH → pH≤1 →
      (Fintype.card V:ℝ)/2≤D₀ → 0≤ε → ε≤ε₀ →
      (∀ v,|(P.degree v:ℝ)-D₀|≤ε*Fintype.card V) → pR*D₀=2*(Fintype.card U:ℝ)*pH →
    ∀ (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j : Color),(∀ u,s u j=pH) →
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
  have hθlo : (if r=3 then (3/4:ℝ) else 1/2)≤θ := by
    by_cases hr3 : r=3
    · subst r
      simpa only [ite_true] using cycleThreshold_triangle_lower.trans hθ
    · simpa only [if_neg hr3] using (cycleThreshold_half_le hr).trans hθ
  obtain ⟨c,B,hc,hB,Nw,hNw,hweights⟩ := positive_ordinary_fractional_cycle_weights r hr α hα
  obtain ⟨k,hk,β,hβ,href⟩ := ordinary_full_host_reference_event r hr θ α pstar ω c B
    hθlo hα hα1 hθ1 hpstar hpstar1 hω hc hB
  refine ⟨k,β,c,B,hk,hβ,hc,hB,?_⟩
  intro η hη
  obtain ⟨ε₀,hε₀,href⟩ := href η hη
  refine ⟨ε₀,hε₀,?_⟩
  intro L hL d q₀ hd
  obtain ⟨N,hN⟩ := href L hL d q₀ hd
  refine ⟨max Nw N,?_⟩
  intro V _ _ hn P hP
  have hn0 : (0:ℝ)≤Fintype.card V := Nat.cast_nonneg _
  obtain ⟨weight,hw,he⟩ := hweights V (by omega) P
    (fun v=>(mul_le_mul_of_nonneg_right (add_le_add hθ (le_refl α)) hn0).trans (hP v))
  have he' := ordinary_cycle_incidence_load_adjacency P r weight he
  refine ⟨weight,hw,he',?_⟩
  intro U Γ Color _ _ _ _ hmlo hmhi F π hF hclose hnoshort pR pH D₀ ε hRlo hRhi hHlo hHhi
    hD hε hεsmall hdeg hbalance q hq hQ s hs hS j hj
  exact hN V U Γ Color (by omega) hmlo hmhi P F π hP hF hclose hnoshort
    pR pH D₀ ε hRlo hRhi hHlo hHhi hD hε hεsmall hdeg hbalance q hq hQ s hs hS j hj weight hw he'

theorem ordinary_full_host_sampling
    (r : ℕ) (hr : 3≤r) (θ α pstar ω : ℝ)
    (hθ : cycleThreshold r≤θ) (hα : 0<α)
    (hpstar : 0<pstar) (hpstar1 : pstar≤1) (hω : 0<ω) :
    ∃ (k : ℕ) (β c B : ℝ),r+2≤k ∧ 0<β ∧ 0<c ∧ 0<B ∧ ∀ η : ℝ,0<η →
    ∃ ε₀ : ℝ,0<ε₀ ∧ ∀ L : ℝ,0≤L → ∀ d q₀ : ℕ,∀ hd : 2≤d,∃ N : ℕ,
    ∀ (V : Type) [Fintype V] [DecidableEq V],N≤Fintype.card V →
    ∀ P : SimpleGraph V,(∀ v,(θ+α)*Fintype.card V≤(P.degree v:ℝ)) →
    ∃ weight : OrdinaryCycle P r → ℝ,
      (∀ C,c/(Fintype.card V:ℝ)^(r-2)≤weight C ∧ weight C≤B/(Fintype.card V:ℝ)^(r-2)) ∧
      (∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0) ∧
    ∀ (U Γ Color : Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U],
      ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ (F : SimpleGraph V) (π : Equiv.Perm V),
      (∀ v,(F.degree v:ℝ)≤L) → permutationConflictGraph π (3*d)≤F →
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ pR pH D₀ ε : ℝ,∀ hRlo : pstar≤pR,∀ hRhi : pR≤1,pstar≤pH → pH≤1 →
      (Fintype.card V:ℝ)/2≤D₀ → 0≤ε → ε≤ε₀ →
      (∀ v,|(P.degree v:ℝ)-D₀|≤ε*Fintype.card V) → pR*D₀=2*(Fintype.card U:ℝ)*pH →
    ∀ (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (j : Color),(∀ u,s u j=pH) →
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
  by_cases hsmall : θ+α<1
  · have hhalf := (cycleThreshold_half_le hr).trans hθ
    exact ordinary_full_host_sampling_numerical r hr θ α pstar ω hθ hα
      (by linarith only [hhalf,hsmall]) (by linarith only [hsmall,hα]) hpstar hpstar1 hω
  · refine ⟨r+2,1,1,1,le_rfl,by norm_num,by norm_num,by norm_num,?_⟩
    intro η hη
    refine ⟨1,by norm_num,?_⟩
    intro L hL d q₀ hd
    refine ⟨1,?_⟩
    intro V _ _ hn P hP
    obtain ⟨v⟩ := Fintype.card_pos_iff.mp (show 0<Fintype.card V by omega)
    have hless : (P.degree v:ℝ)<Fintype.card V := by exact_mod_cast P.degree_lt_card_verts v
    have hlow := mul_le_mul_of_nonneg_right (le_of_not_gt hsmall) (Nat.cast_nonneg (Fintype.card V) : (0:ℝ)≤Fintype.card V)
    exfalso
    linarith only [hP v,hless,hlow]

end Oberwolfach
