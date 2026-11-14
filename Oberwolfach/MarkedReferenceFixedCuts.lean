module

public import Oberwolfach.ExponentialMarkedReferenceCuts

@[expose] public section

/-! The source numerical cut parameters follow from the stronger cut
families; the ordinary rim coefficient is retained explicitly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem markedReferenceCutFamilies_fixed_cuts
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (g : Γ) (j : Color)
    (α kstar tstar p k : ℝ) (hα : 0<α) (hkstar : 0<kstar) (htstar : 0<tstar)
    (hpmin : kstar≤p) (hkmin : kstar≤k) (hn : 0<Fintype.card V)
    (σ : RawMarkedOutcome V U Γ Color)
    (hcuts : MarkedReferenceCutFamilies P π d g j α p k tstar σ) :
    let δ := min (min α kstar) tstar/256
    let h := min (α*kstar) tstar/128
    (∀ b : Bool,∀ (X : Finset V) (Y : Finset U),
      1-2*δ<(X.card:ℝ)/Fintype.card V+(Y.card:ℝ)/Fintype.card U →
      16*h*min ((Fintype.card U:ℝ)*X.card) ((Fintype.card V:ℝ)*Y.card)≤
        (bipartiteMatrixCut (fun v u=>if rawMarkedPairSpokes π d σ g j b v u then 1 else 0) X Y:ℝ)) ∧
    (∀ b : Bool,∀ S T : Finset V,
      1-2*δ<(S.card:ℝ)/Fintype.card V+(T.card:ℝ)/Fintype.card V →
      16*h*min ((Fintype.card V:ℝ)*S.card) ((Fintype.card V:ℝ)*T.card)≤
        (matrixCut (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) b) S T:ℝ)) := by
  intro δ h
  let n := Fintype.card V
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
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
    have hh := hcuts.1 b X Y (by linarith only [hlarge,hδt])
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
    have hh := hcuts.2 b δ hδα (by linarith only [hδk,hcoef]) S T hlarge'
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


theorem markedReferenceCutFamilies_ordinary_cut
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (g : Γ) (j : Color)
    (α p k tstar : ℝ) (hα : 0≤α) (hp : 0≤p)
    (σ : RawMarkedOutcome V U Γ Color)
    (hcuts : MarkedReferenceCutFamilies P π d g j α p k tstar σ)
    (S T : Finset V)
    (hlarge : (1-2*min (α/64) (p/128))*Fintype.card V<(S.card:ℝ)+T.card) :
    (α*p/4)*Fintype.card V*min (S.card:ℝ) T.card≤
      (matrixCut (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) false) S T:ℝ) := by
  have hδα : min (α/64) (p/128)≤α/32 := (min_le_left _ _).trans (by linarith)
  have hδp : min (α/64) (p/128)≤p/32 := (min_le_right _ _).trans (by linarith)
  exact hcuts.2 false _ hδα hδp S T hlarge

end Oberwolfach
