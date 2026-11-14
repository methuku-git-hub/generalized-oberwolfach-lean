module

public import Oberwolfach.OrdinaryExpansionMaps

@[expose] public section

/-! The part-preserving collapse of expansion spokes is bijective on
actual spokes, even when the original row and hub maps are not injective. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V V' U U' E J W : Type*}

theorem ordinaryExpansion_spoke_hom (z : W) (v : J → V) (u : J → U) (f : V → V') (g : U → U')
    (a : ExpansionRow V E J W) (b : ExpansionHub U E J) (h : ordinaryExpansionSpokes z v u a b) :
    ordinaryExpansionSpokes z (f ∘ v) (g ∘ u) (expansionRowMap f a) (expansionHubMap g b) := by
  cases a with
  | inl a =>
    cases b with
    | inl b => exact h.elim
    | inr i =>
      cases i with
      | inl e => exact h.elim
      | inr j => exact congrArg f h
  | inr p =>
    rcases p with ⟨i,w⟩
    cases i with
    | inl e => cases b <;> exact h
    | inr j =>
      cases b with
      | inl b => exact ⟨h.1,congrArg g h.2⟩
      | inr i => exact h

theorem ordinaryExpansion_spoke_preimage (z : W) (v : J → V) (u : J → U) (f : V → V') (g : U → U')
    (a : ExpansionRow V' E J W) (b : ExpansionHub U' E J)
    (h : ordinaryExpansionSpokes z (f ∘ v) (g ∘ u) a b) :
    ∃ a' b',ordinaryExpansionSpokes z v u a' b' ∧ expansionRowMap f a'=a ∧ expansionHubMap g b'=b := by
  cases a with
  | inl a =>
    cases b with
    | inl b => exact h.elim
    | inr i =>
      cases i with
      | inl e => exact h.elim
      | inr j => exact ⟨.inl (v j),.inr (.inr j),rfl,congrArg Sum.inl h.symm,rfl⟩
  | inr p =>
    rcases p with ⟨i,w⟩
    cases i with
    | inl e =>
      cases b with
      | inl b => exact h.elim
      | inr i => exact ⟨.inr (.inl e,w),.inr i,h,rfl,rfl⟩
    | inr j =>
      cases b with
      | inl b => exact ⟨.inr (.inr j,w),.inl (u j),⟨h.1,rfl⟩,rfl,congrArg Sum.inl h.2.symm⟩
      | inr i => exact ⟨.inr (.inr j,w),.inr i,h,rfl,rfl⟩

theorem ordinaryExpansion_spoke_pair_injective (z : W) (v : J → V) (u : J → U)
    (f : V → V') (g : U → U')
    (a c : ExpansionRow V E J W) (b d : ExpansionHub U E J)
    (hab : ordinaryExpansionSpokes z v u a b) (hcd : ordinaryExpansionSpokes z v u c d)
    (hac : expansionRowMap f a=expansionRowMap f c) (hbd : expansionHubMap g b=expansionHubMap g d) :
    a=c ∧ b=d := by
  cases a with
  | inl a =>
    cases c with
    | inr p => cases hac
    | inl c =>
      cases b with
      | inl b => exact hab.elim
      | inr i =>
        cases d with
        | inl d => cases hbd
        | inr i' =>
          have hii : i=i' := Sum.inr.inj hbd
          subst i'
          cases i with
          | inl e => exact hab.elim
          | inr j => exact ⟨congrArg Sum.inl (hab.trans hcd.symm),rfl⟩
  | inr p =>
    cases c with
    | inl c => cases hac
    | inr q =>
      have hpq : p=q := Sum.inr.inj hac
      subst q
      cases b with
      | inl b =>
        cases d with
        | inr i => cases hbd
        | inl d =>
          rcases p with ⟨i,w⟩
          cases i with
          | inl e => exact hab.elim
          | inr j => exact ⟨rfl,congrArg Sum.inl (hab.2.trans hcd.2.symm)⟩
      | inr i =>
        cases d with
        | inl d => cases hbd
        | inr i' => exact ⟨rfl,congrArg Sum.inr (Sum.inr.inj hbd)⟩

theorem ordinaryExpansion_spoke_injective (z : W) (v : J → V) (u : J → U)
    (f : V → V') (g : U → U') :
    Set.InjOn (Prod.map (expansionRowMap (E:=E) (W:=W) f) (expansionHubMap g))
      {e | ordinaryExpansionSpokes z v u e.1 e.2} := by
  rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd hh
  have ha := congrArg Prod.fst hh
  have hb := congrArg Prod.snd hh
  exact Prod.ext (ordinaryExpansion_spoke_pair_injective z v u f g a c b d hab hcd ha hb).1
    (ordinaryExpansion_spoke_pair_injective z v u f g a c b d hab hcd ha hb).2

end Oberwolfach
