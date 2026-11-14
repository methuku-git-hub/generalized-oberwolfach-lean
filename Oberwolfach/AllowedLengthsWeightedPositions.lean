module

public import Oberwolfach.SelectedLengthsWeightedPositions
public import Oberwolfach.TwoComponentLower

@[expose] public section
/-! The common weight and position bounds apply to any allowed set chosen
after the order threshold, using its actual supremum threshold. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem allowed_lengths_weighted_positional_data
    (K d:ℕ) (n:Fin K→ℕ) (hn:∀ i,1≤n i) (α τ:ℝ) (hα:0<α) (hτ:0<τ):
    ∃ B:Fin K→ℝ,(∀ i,0<B i) ∧ ∃ N:ℕ,1≤N ∧
    ∀ (V:Type) [Fintype V] [DecidableEq V],N≤Fintype.card V→
    ∀ (S:Finset (Fin K)) (Allowed:Set ℕ) (G:SimpleGraph V) (D ε:ℝ),
      ((Fintype.card V:ℝ)/2≤D)→ε≤τ/4→
      (∀ i:{i:Fin K // i∈S},n i.val+2∈Allowed)→
      (∀ v,(allowedThreshold Allowed+α)*Fintype.card V≤(G.degree v:ℝ))→
    ∃ w:∀ i:{i:Fin K // i∈S},OrdinaryCycle G (n i.val+2)→ℝ,
      (∀ i C,0≤w i C ∧ w i C≤B i.val/(Fintype.card V:ℝ)^(n i.val)) ∧
      (∀ i x y,(∑ C,if C.val.val.Adj x y then w i C else 0)=if G.Adj x y then 1 else 0) ∧
      (∀ i:{i:Fin K // i∈S},5*((n i.val+2:ℕ):ℝ)^4*B i.val*(2*(3*d))/Fintype.card V≤τ ∧
        6*((n i.val+2:ℕ):ℝ)^4*B i.val*(2*(3*d))+ε*(Fintype.card V:ℝ)≤τ*D):=by
  classical
  obtain ⟨B,hB,N,hN,hw⟩:=selected_lengths_weighted_positional_data K d n hn α τ hα hτ
  refine ⟨B,hB,N,hN,?_⟩
  intro V _ _ hN' S Allowed G D ε hD hε hmem hdeg
  apply hw V hN' S G D ε hD hε
  intro i v
  have hbdd:BddAbove (cycleThreshold '' Allowed):=by
    refine ⟨1,?_⟩
    rintro x ⟨r,hr,rfl⟩
    exact cycleThreshold_le_one r
  have hle:cycleThreshold (n i.val+2)≤allowedThreshold Allowed:=
    le_csSup hbdd ⟨n i.val+2,hmem i,rfl⟩
  have hh:(cycleThreshold (n i.val+2)+α)*(Fintype.card V:ℝ)≤
      (allowedThreshold Allowed+α)*(Fintype.card V:ℝ):=
    mul_le_mul_of_nonneg_right (by linarith [hle]) (Nat.cast_nonneg _)
  exact hh.trans (hdeg v)
end Oberwolfach
