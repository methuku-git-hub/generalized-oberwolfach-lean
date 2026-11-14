module

public import Oberwolfach.RawMarkedSpokeCuts
public import Oberwolfach.MarkedPhysicalCuts
public import Oberwolfach.ProductGoodEvents

@[expose] public section

/-! The four initial marked incidence graphs satisfy their fixed large-cut
bounds on one sample. The physical coordinates and interval coordinates
retain the two independent exposures of the manuscript. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_reference_large_cuts
    (α kstar tstar ω : ℝ) (hα : 0<α) (hα1 : α≤1/2)
    (hkstar : 0<kstar) (htstar : 0<tstar) (htstar1 : tstar≤1) (hω : 0<ω)
    (d q₀ : ℕ) (hd : 2≤d) :
    ∃ N : ℕ,∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ P : SimpleGraph V,(∀ x,(1/2+α)*Fintype.card V≤(P.degree x:ℝ)) →
    ∀ (π : Equiv.Perm V),(∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (p k : ℝ) (hp : 0≤p) (hk : 0≤k) (hsum : 2*p+2*k≤1),kstar≤p → kstar≤k →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (g : Γ) (j : Color) (s₀ t₀ : ℝ),(∀ u,q u g=t₀) → (∀ u,s u j=s₀) → tstar≤s₀ → tstar≤t₀ →
    let δ := min (min α kstar) tstar/256
    let h := min (α*kstar) tstar/128
    let μ := (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).prod
      (FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum))
    1-1/(Fintype.card V:ℝ)^q₀≤μ.probability (fun z=>
      (∀ b : Bool,∀ (X : Finset V) (Y : Finset U),
        1-2*δ<(X.card:ℝ)/Fintype.card V+(Y.card:ℝ)/Fintype.card U →
        16*h*min ((Fintype.card U:ℝ)*X.card) ((Fintype.card V:ℝ)*Y.card)≤
          (bipartiteMatrixCut (fun v u=>if rawMarkedSpokes π d z.1 g j b v u then 1 else 0) X Y:ℝ)) ∧
      (∀ b : Bool,∀ S T : Finset V,
        1-2*δ<(S.card:ℝ)/Fintype.card V+(T.card:ℝ)/Fintype.card V →
        16*h*min ((Fintype.card V:ℝ)*S.card) ((Fintype.card V:ℝ)*T.card)≤
          (matrixCut (markedPhysicalRim P π (3*d) z.2 b) S T:ℝ))) := by
  obtain ⟨N₁,hN₁⟩ := rawMarked_spoke_cuts tstar ω htstar htstar1 hω d (q₀+1) hd
  obtain ⟨N₂,hN₂⟩ := markedPhysical_large_cuts α kstar hα hα1 hkstar (3*d) (q₀+1)
  refine ⟨max 2 (max N₁ N₂),?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN hmlo hmhi P hP π hnoshort p k hp hk hsum hpmin hkmin q hq hQ s hs hS g j s₀ t₀ hg hj hslo htlo
  let n := Fintype.card V
  let δ := min (min α kstar) tstar/256
  let h := min (α*kstar) tstar/128
  have hn : 0<n := by dsimp [n];omega
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  let μ := FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  let ν := FiniteLaw.pi (fun _ : Sym2 V=>markedPhysicalLaw p k hp hk hsum)
  have hsp := hN₁ V U Γ Color (by omega) hmlo hmhi π q hq hQ s hs hS g j s₀ t₀ hg hj hslo htlo hnoshort
  have hph := hN₂ V (by omega) P hP π p k hp hk hsum hpmin hkmin
  let E := fun σ : RawIntervalFamilyOutcome V U Γ Color=>∀ b : Bool,∀ (X : Finset V) (Y : Finset U),
    1-tstar/8<(X.card:ℝ)/Fintype.card V+(Y.card:ℝ)/Fintype.card U →
    tstar/8*min ((Fintype.card U:ℝ)*X.card) ((Fintype.card V:ℝ)*Y.card)≤
      (bipartiteMatrixCut (fun v u=>if rawMarkedSpokes π d σ g j b v u then 1 else 0) X Y:ℝ)
  let F := fun σ : Sym2 V→Option (Bool×Bool)=>∀ b : Bool,∀ δ' : ℝ,δ'≤α/32 → δ'≤(if b then k else p)/32 →
    ∀ S T : Finset V,(1-2*δ')*Fintype.card V<(S.card:ℝ)+T.card →
    (α*(if b then k else p)/4)*Fintype.card V*min (S.card:ℝ) T.card≤
      (matrixCut (markedPhysicalRim P π (3*d) σ b) S T:ℝ)
  have hjoint := finiteLaw_product_good_lower μ ν E (fun _ σ=>F σ)
    (1/(n:ℝ)^(q₀+1)) (1/(n:ℝ)^(q₀+1)) (by positivity) hsp (fun _ _=>hph)
  have hsumerr := scaled_inverse_power_le n q₀ hn 2 (by exact_mod_cast (show 2≤n by dsimp [n];omega))
  have hbound : 1-1/(n:ℝ)^q₀≤1-1/(n:ℝ)^(q₀+1)-1/(n:ℝ)^(q₀+1) := by
    convert sub_le_sub_left hsumerr 1 using 1 <;> ring
  apply (hbound.trans hjoint).trans
  apply finiteLaw_probability_mono
  intro z hz
  have hδα : δ≤α/32 := by
    have hh := (min_le_left (min α kstar) tstar).trans (min_le_left α kstar)
    dsimp [δ];linarith only [hh,hα]
  have hδk : δ≤kstar/32 := by
    have hh := (min_le_left (min α kstar) tstar).trans (min_le_right α kstar)
    dsimp [δ];linarith only [hh,hkstar]
  have hδt : 2*δ≤tstar/8 := by
    have hh := min_le_right (min α kstar) tstar
    dsimp [δ];linarith only [hh,htstar]
  constructor
  · intro b X Y hlarge
    change 1-2*δ<(X.card:ℝ)/Fintype.card V+(Y.card:ℝ)/Fintype.card U at hlarge
    have hh := hz.1 b X Y (by linarith only [hlarge,hδt])
    have hc : 16*h≤tstar/8 := by
      have hh := min_le_right (α*kstar) tstar
      dsimp [h];linarith only [hh]
    exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans hh
  · intro b S T hlarge
    have hcoef : kstar≤(if b then k else p) := by cases b <;> assumption
    have hlarge' : (1-2*δ)*Fintype.card V<(S.card:ℝ)+T.card := by
      have hh := mul_lt_mul_of_pos_right hlarge hn0
      have heq : ((S.card:ℝ)/n+(T.card:ℝ)/n)*n=(S.card:ℝ)+T.card := by field_simp
      change (1-2*δ)*(n:ℝ)<((S.card:ℝ)/n+(T.card:ℝ)/n)*n at hh
      rw [heq] at hh
      exact hh
    have hh := hz.2 b δ hδα (by linarith only [hδk,hcoef]) S T hlarge'
    have hc : 16*h≤α*(if b then k else p)/4 := by
      have hh := min_le_left (α*kstar) tstar
      have hm := mul_le_mul_of_nonneg_left hcoef hα.le
      dsimp [h];nlinarith only [hh,hm,mul_pos hα hkstar]
    rw [← mul_min_of_nonneg _ _ hn0.le]
    change 16*h*((n:ℝ)*min (S.card:ℝ) T.card)≤_
    calc
      _ = (16*h*(n:ℝ))*min (S.card:ℝ) T.card := by ring
      _ ≤ (α*(if b then k else p)/4*(n:ℝ))*min (S.card:ℝ) T.card :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hn0.le)
          (le_min (Nat.cast_nonneg S.card) (Nat.cast_nonneg T.card))
      _ ≤ _ := hh

end Oberwolfach
