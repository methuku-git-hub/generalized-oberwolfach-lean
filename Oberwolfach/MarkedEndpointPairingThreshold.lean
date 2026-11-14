module

public import Oberwolfach.MarkedTypedEndpointPairing

@[expose] public section

/-! The source endpoint-pairing hierarchy, with the order threshold chosen
after the permutation radius, label multiplicity and density constants. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_endpoint_pairing_threshold
    (b M : ℕ) (κ lam ε : ℝ) (hκ : 0<κ) (hlam : 0<lam)
    (hε : 0<ε) (hεκ : ε<κ/8) (hepslam : ε<lam/8) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀≤s →
    ∀ (A X Y V : Type) [Fintype A] [Fintype X] [Fintype Y] [Fintype V],
    ∀ (EA : A → Y → Prop) (EX : X → Y → Prop)
      (PA : A → Prop) (PX : X → Prop) (Q : Y → Prop),
      Fintype.card A=s → Fintype.card X=s → Fintype.card Y=s →
      Fintype.card {a // PA a}=Fintype.card {y // Q y} →
      ((Finset.univ.filter Q).card:ℝ)+(Finset.univ.filter PX).card≤(1-κ)*s →
      (∀ x y, EX x y → PX x → ¬Q y) →
    ∀ (π : Equiv.Perm V) (labelA : A → V) (labelX : X → V),
      (∀ v, Fintype.card {a // labelA a=v}≤M) →
      (∀ v, Fintype.card {x // labelX x=v}≤M) →
      BipartiteBlockBounds EA PA Q (2*lam*s) (ε*s) lam →
      BipartiteBlockBounds EA (fun x => ¬PA x) (fun y => ¬Q y) (2*lam*s) (ε*s) lam →
      BipartiteBlockBounds EX PX (fun y => ¬Q y) (2*lam*s) (ε*s) lam →
      BipartiteBlockBounds EX (fun x => ¬PX x) (fun y => ¬Q y) (2*lam*s) (ε*s) lam →
      BipartiteBlockBounds EX (fun x => ¬PX x) Q (2*lam*s) (ε*s) lam →
      ∃ f : A ≃ Y, ∃ g : X ≃ Y,
        (∀ x, EA x (f x)) ∧ (∀ x, EX x (g x)) ∧
        (∀ x, Q (f x) ↔ PA x) ∧ (∀ x, PX x → ¬Q (g x)) ∧
        ∀ y, ¬PermutationClose π b (labelA (f.symm y)) (labelX (g.symm y)) := by
  let C : ℝ := (M*(2*b+1):ℕ)
  obtain ⟨s₀,hs₀⟩ := exists_nat_gt (max 1 (max (C/lam) (C/(lam*ε))))
  refine ⟨s₀,?_⟩
  intro s hs A X Y V _ _ _ _ EA EX PA PX Q hA hX hY hclass hsize hallowed π labelA labelX hfA hfX B₁ B₂ B₃ B₄ B₅
  have hsr : (s₀:ℝ)≤s := Nat.cast_le.mpr hs
  have hspos : (0:ℝ)<s := by
    have hh := (le_max_left 1 (max (C/lam) (C/(lam*ε)))).trans_lt (hs₀.trans_le hsr)
    linarith
  have hC₁ : C<lam*s := by
    have hh := (le_max_left (C/lam) (C/(lam*ε))).trans (le_max_right 1 _)
    have hh' := (div_lt_iff₀ hlam).mp (hh.trans_lt (hs₀.trans_le hsr))
    nlinarith only [hh']
  have hC₂ : C<lam*(ε*s) := by
    have hh := (le_max_right (C/lam) (C/(lam*ε))).trans (le_max_right 1 _)
    have hh' := (div_lt_iff₀ (mul_pos hlam hε)).mp (hh.trans_lt (hs₀.trans_le hsr))
    nlinarith only [hh']
  have hdegree : 2*(ε*s)+C≤2*lam*s := by
    have hh := mul_lt_mul_of_pos_right hepslam hspos
    nlinarith only [hh,hC₁,mul_pos hε hspos]
  have hsplit : ((Finset.univ.filter Q).card:ℝ)+
      (Finset.univ.filter (fun y => ¬Q y)).card=s := by
    have hh := Finset.card_filter_add_card_filter_not (s:=(Finset.univ:Finset Y)) Q
    rw [Finset.card_univ,hY] at hh
    exact_mod_cast hh
  have hgap : ((Finset.univ.filter PX).card:ℝ)+2*(ε*s)≤
      (Finset.univ.filter (fun y => ¬Q y)).card := by
    have hh := mul_lt_mul_of_pos_right hεκ hspos
    nlinarith only [hsize,hsplit,hh,mul_pos hε hspos]
  exact marked_typed_endpoint_pairing_of_bounds EA EX PA PX Q
    (hA.trans hY.symm) (hX.trans hY.symm) hclass hallowed π b M labelA labelX hfA hfX
    (2*lam*s) (ε*s) lam (mul_pos hε hspos) hlam hdegree hC₂ hgap B₁ B₂ B₃ B₄ B₅

end Oberwolfach
