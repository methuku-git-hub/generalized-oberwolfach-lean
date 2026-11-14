module

public import Oberwolfach.MarkedPathParent

@[expose] public section

/-! Lower counts for the actual parent paths, obtained by an injective
reordering of the verified greedy choices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem denseRootMarkedPath_count {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V) (π : Equiv.Perm V) (b r : ℕ) (hr : 1≤r) (j : Bool)
    (T₀ TK : Finset V) (v v' : V) (α a : ℝ) (hα : 0≤α) (hα1 : α≤1) (ha : 0≤a)
    (hbudget : a≤α*min (T₀.card:ℝ) TK.card-((r:ℝ)+6)*(2*(b:ℝ)+1))
    (hdeg₀ : ∀ x : V,(1/2+α/2)*T₀.card≤((P.neighborFinset x∩T₀).card:ℝ))
    (hdegK : ∀ x : V,(1/2+α/2)*TK.card≤((P.neighborFinset x∩TK.image π).card:ℝ)) :
    a^(r+4)≤(Fintype.card {z : Fin (r+4)→V // DenseRootMarkedPath P π b j T₀ TK v v' z}:ℝ) := by
  have hh := marked_path_choice_count P π b (r+4) j T₀ TK v v' α a hα hα1 ha
    (by simpa only [Nat.cast_add,Nat.cast_ofNat,add_assoc,show (4:ℝ)+2=6 by norm_num] using hbudget) hdeg₀ hdegK
  let I := {f : Fin (r+4)→V //
    MixedGreedyGood P π b (markedPathChoiceClass j T₀ TK) (markedPathChoiceHead π j)
      (markedPathChoiceRequests π j (r+4) v v') {v,v'} f}
  let J := {z : Fin (r+4)→V // DenseRootMarkedPath P π b j T₀ TK v v' z}
  let inj : I→J := fun f=>⟨fun i=>f.val (pathChoiceOrder (r+2) i),
    markedPathChoice_to_parent P π b r hr j T₀ TK v v' f.val f.property⟩
  have hi : Function.Injective inj := by
    intro f g he
    apply Subtype.ext
    funext i
    have hh := congrArg (fun z : J=>z.val ((pathChoiceOrder (r+2)).symm i)) he
    simpa only [inj,Equiv.apply_symm_apply] using hh
  exact hh.trans (by exact_mod_cast Fintype.card_le_of_injective inj hi)

theorem denseRootMarkedPath_uniform_density
    (r b : ℕ) (hr : 1≤r) (α θ : ℝ) (hα : 0<α) (hα1 : α≤1) (hθ : 0<θ) :
    ∃ N : ℕ,∀ (V : Type) [Fintype V] [DecidableEq V],N≤Fintype.card V →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V) (T₀ TK : Finset V),
      θ*Fintype.card V≤(T₀.card:ℝ) → θ*Fintype.card V≤(TK.card:ℝ) →
      (∀ x : V,(1/2+α/2)*T₀.card≤((P.neighborFinset x∩T₀).card:ℝ)) →
      (∀ x : V,(1/2+α/2)*TK.card≤((P.neighborFinset x∩TK.image π).card:ℝ)) →
    ∀ (j : Bool) (v v' : V),
    (α*θ/4)^(r+4)*(Fintype.card V:ℝ)^(r+4)≤
      (Fintype.card {z : Fin (r+4)→V // DenseRootMarkedPath P π b j T₀ TK v v' z}:ℝ) := by
  obtain ⟨N,hN⟩ := exists_nat_ge ((((r:ℝ)+6)*(2*(b:ℝ)+1))/(α*θ/4))
  refine ⟨N,?_⟩
  intro V _ _ hn P π T₀ TK h₀ hK hd₀ hdK j v v'
  have hnR : (N:ℝ)≤Fintype.card V := by exact_mod_cast hn
  have hmargin := (div_le_iff₀ (show 0<α*θ/4 by positivity)).mp (hN.trans hnR)
  have hsize := mul_le_mul_of_nonneg_left (le_min h₀ hK) hα.le
  have hbudget : (α*θ/4)*Fintype.card V≤α*min (T₀.card:ℝ) TK.card-
      ((r:ℝ)+6)*(2*(b:ℝ)+1) := by
    have hpos : 0≤α*θ*Fintype.card V := by positivity
    nlinarith only [hsize,hmargin,hpos]
  have hh := denseRootMarkedPath_count P π b r hr j T₀ TK v v' α ((α*θ/4)*Fintype.card V)
    hα.le hα1 (by positivity) hbudget hd₀ hdK
  simpa only [mul_pow] using hh

end Oberwolfach
