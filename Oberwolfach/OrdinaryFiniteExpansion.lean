module

public import Oberwolfach.CanonicalGraphPairs
public import Oberwolfach.CycleCopies

@[expose] public section

/-! Explicit finite expansions of indexed rim pairs and spokes. Original
rim pairs may be loops or repeat: every replacement uses its own private
wheel vertices, so the resulting graph is a simple graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E J W : Type*}

abbrev ExpansionRow (V E J W : Type*) := V ⊕ ((E ⊕ J) × W)
abbrev ExpansionHub (U E J : Type*) := U ⊕ (E ⊕ J)

abbrev expansionPrivateAdj (C : SimpleGraph W) (z o : W) :
    E ⊕ J → W → W → Prop
  | Sum.inl _,a,b => C.Adj a b ∧ ¬ ((a=z ∧ b=o) ∨ (a=o ∧ b=z))
  | Sum.inr _,a,b => C.Adj a b

abbrev expansionCrossAdj (z o : W) (x y : E → V) : V → (E ⊕ J) × W → Prop
  | a,(Sum.inl e,w) => (a=x e ∧ w=o) ∨ (a=y e ∧ w=z)
  | _,(Sum.inr _,_) => False

abbrev ordinaryExpansionRim (C : SimpleGraph W) (z o : W) (x y : E → V) :
    SimpleGraph (ExpansionRow V E J W) where
  Adj a b := match a,b with
    | Sum.inl _,Sum.inl _ => False
    | Sum.inl a,Sum.inr p => expansionCrossAdj z o x y a p
    | Sum.inr p,Sum.inl a => expansionCrossAdj z o x y a p
    | Sum.inr (i,w),Sum.inr (j,w') => i=j ∧ expansionPrivateAdj C z o i w w'
  symm := ⟨by
    intro a b hab
    cases a with
    | inl a => cases b <;> exact hab
    | inr p =>
      cases b with
      | inl b => exact hab
      | inr q =>
        rcases p with ⟨i,w⟩; rcases q with ⟨j,w'⟩
        obtain ⟨rfl,h⟩ := hab
        refine ⟨rfl,?_⟩
        cases i <;> simp only [expansionPrivateAdj] at h ⊢
        · exact ⟨h.1.symm,by tauto⟩
        · exact h.symm⟩
  loopless := ⟨by
    intro a
    cases a with
    | inl a => exact not_false
    | inr p =>
      rcases p with ⟨i,w⟩
      intro h
      cases i <;> simp only [expansionPrivateAdj] at h
      · exact h.2.1.ne rfl
      · exact h.2.ne rfl⟩

theorem expansionRim_adj_old_old (C : SimpleGraph W) (z o : W) (x y : E → V) (a b : V) :
    (ordinaryExpansionRim (J:=J) C z o x y).Adj (.inl a) (.inl b) ↔ False := Iff.rfl

theorem expansionRim_adj_old_private (C : SimpleGraph W) (z o : W) (x y : E → V)
    (a : V) (p : (E ⊕ J) × W) :
    (ordinaryExpansionRim C z o x y).Adj (.inl a) (.inr p) ↔ expansionCrossAdj z o x y a p := Iff.rfl

theorem expansionRim_adj_private_old (C : SimpleGraph W) (z o : W) (x y : E → V)
    (a : V) (p : (E ⊕ J) × W) :
    (ordinaryExpansionRim C z o x y).Adj (.inr p) (.inl a) ↔ expansionCrossAdj z o x y a p := Iff.rfl

theorem expansionRim_adj_private_private (C : SimpleGraph W) (z o : W) (x y : E → V)
    (i j : E ⊕ J) (w w' : W) :
    (ordinaryExpansionRim C z o x y).Adj (.inr (i,w)) (.inr (j,w')) ↔
      i=j ∧ expansionPrivateAdj C z o i w w' := Iff.rfl

theorem expansionCrossAdj_rim (z o : W) (x y : E → V) (a : V) (e : E) (w : W) :
    expansionCrossAdj (J:=J) z o x y a (.inl e,w) ↔ (a=x e ∧ w=o) ∨ (a=y e ∧ w=z) := Iff.rfl

theorem expansionCrossAdj_spoke (z o : W) (x y : E → V) (a : V) (j : J) (w : W) :
    expansionCrossAdj z o x y a (.inr j,w) ↔ False := Iff.rfl

abbrev ordinaryExpansionSpokes (z : W) (v : J → V) (u : J → U) :
    ExpansionRow V E J W → ExpansionHub U E J → Prop
  | Sum.inl _,Sum.inl _ => False
  | Sum.inl _,Sum.inr (Sum.inl _) => False
  | Sum.inl a,Sum.inr (Sum.inr j) => a=v j
  | Sum.inr (Sum.inl _,_),Sum.inl _ => False
  | Sum.inr (Sum.inr j,w),Sum.inl b => w=z ∧ b=u j
  | Sum.inr (Sum.inl e,_),Sum.inr i => i=Sum.inl e
  | Sum.inr (Sum.inr j,w),Sum.inr i => w≠z ∧ i=Sum.inr j

theorem ordinaryExpansion_no_old_rim (C : SimpleGraph W) (z o : W) (x y : E → V)
    (a b : V) : ¬ (ordinaryExpansionRim (J:=J) C z o x y).Adj (.inl a) (.inl b) := not_false

theorem ordinaryExpansion_no_old_spoke (z : W) (v : J → V) (u : J → U)
    (a : V) (b : U) : ¬ ordinaryExpansionSpokes (E:=E) z v u (.inl a) (.inl b) := not_false

section Finite
variable [Fintype V] [Fintype U] [Fintype E] [Fintype J] [Fintype W]
variable [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq J] [DecidableEq W]

def naturalIndicator (p : Prop) : ℕ := if p then 1 else 0

theorem naturalIndicator_true : naturalIndicator True = 1 := by simp [naturalIndicator]
theorem naturalIndicator_false : naturalIndicator False = 0 := by simp [naturalIndicator]

theorem naturalIndicator_and (p q : Prop) :
    naturalIndicator (p ∧ q) = if p then naturalIndicator q else 0 := by
  by_cases hp : p <;> simp [naturalIndicator,hp]

theorem naturalIndicator_sum_eq {A : Type*} [Fintype A] (a : A) :
    (∑ b : A,naturalIndicator (b=a))=1 := by simp [naturalIndicator]

theorem naturalIndicator_sum_eq_rev {A : Type*} [Fintype A] (a : A) :
    (∑ b : A,naturalIndicator (a=b))=1 := by simp [naturalIndicator]

theorem graph_degree_indicator_sum {A : Type*} [Fintype A] (G : SimpleGraph A) (a : A) :
    G.degree a = ∑ b : A,naturalIndicator (G.Adj a b) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have h : G.neighborFinset a = Finset.univ.filter (G.Adj a) := by ext; simp
  rw [h,Finset.card_eq_sum_ones,Finset.sum_filter]
  rfl

theorem ordinaryExpansionRim_degree_old (C : SimpleGraph W) (z o : W) (hzo : z≠o)
    (x y : E → V) (a : V) :
    (ordinaryExpansionRim (J:=J) C z o x y).degree (.inl a) =
      (Finset.univ.filter (fun e => a=x e)).card +
      (Finset.univ.filter (fun e => a=y e)).card := by
  rw [graph_degree_indicator_sum,Fintype.sum_sum_type]
  simp only [ordinaryExpansionRim,naturalIndicator_false,Finset.sum_const_zero,zero_add,Fintype.sum_prod_type]
  rw [Fintype.sum_sum_type]
  simp only [expansionCrossAdj,naturalIndicator_false,Finset.sum_const_zero,add_zero]
  have hi (e : E) (w : W) :
      naturalIndicator ((a=x e ∧ w=o) ∨ (a=y e ∧ w=z)) =
      (if a=x e then naturalIndicator (w=o) else 0)+
      (if a=y e then naturalIndicator (w=z) else 0) := by
    by_cases ha : a=x e <;> by_cases hb : a=y e <;> by_cases hw : w=o <;> by_cases hz : w=z
    all_goals simp_all [naturalIndicator]
  simp_rw [hi,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,naturalIndicator_sum_eq]
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]

theorem ordinaryExpansionRim_degree_private (C : SimpleGraph W) (z o : W)
    (hzo : C.Adj z o) (x y : E → V) (i : E ⊕ J) (w : W) :
    (ordinaryExpansionRim C z o x y).degree (.inr (i,w)) = C.degree w := by
  rw [graph_degree_indicator_sum,Fintype.sum_sum_type]
  simp only [ordinaryExpansionRim,Fintype.sum_prod_type]
  have hprivate : (∑ p : E ⊕ J,∑ w' : W,
      naturalIndicator (i=p ∧ expansionPrivateAdj C z o i w w')) =
      ∑ w' : W,naturalIndicator (expansionPrivateAdj C z o i w w') := by
    simp_rw [naturalIndicator_and]
    simp
  rw [hprivate,graph_degree_indicator_sum]
  cases i with
  | inr j => simp [expansionCrossAdj,expansionPrivateAdj,naturalIndicator_false]
  | inl e =>
    have he (a : V) :
        naturalIndicator (expansionCrossAdj (J:=J) z o x y a (Sum.inl e,w)) =
        (if w=o then naturalIndicator (a=x e) else 0)+
        (if w=z then naturalIndicator (a=y e) else 0) := by
      by_cases ha : a=x e <;> by_cases hb : a=y e <;> by_cases hw : w=o <;> by_cases hz : w=z
      all_goals simp_all [expansionCrossAdj,hzo.ne,naturalIndicator]
    simp_rw [he,Finset.sum_add_distrib]
    simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,naturalIndicator_sum_eq]
    have hcount (w' : W) :
        naturalIndicator (expansionPrivateAdj C z o (Sum.inl e : E ⊕ J) w w')+
        naturalIndicator (w=o ∧ w'=z)+naturalIndicator (w=z ∧ w'=o)=
        naturalIndicator (C.Adj w w') := by
      by_cases hw : w=o <;> by_cases hz : w=z <;> by_cases hw' : w'=o <;> by_cases hz' : w'=z
      all_goals simp_all [expansionPrivateAdj,hzo.ne,hzo.symm,naturalIndicator]
    have hs := congrArg (fun f : W → ℕ => ∑ w',f w') (funext hcount)
    have hzsum : (∑ w' : W,naturalIndicator (w=o ∧ w'=z))=if w=o then 1 else 0 := by
      simp only [naturalIndicator_and,Finset.sum_ite_irrel,naturalIndicator_sum_eq,Finset.sum_const_zero]
    have hosum : (∑ w' : W,naturalIndicator (w=z ∧ w'=o))=if w=z then 1 else 0 := by
      simp only [naturalIndicator_and,Finset.sum_ite_irrel,naturalIndicator_sum_eq,Finset.sum_const_zero]
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib,hzsum,hosum] at hs
    omega

end Finite
end Oberwolfach
