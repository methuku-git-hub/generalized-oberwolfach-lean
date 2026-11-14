module

public import Oberwolfach.OrdinaryFiniteExpansion
public import Oberwolfach.FractionalRelabeling

@[expose] public section

/-! A private cycle attached at one prescribed old vertex. Several
attachments may share their old vertex, but have no other common vertex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I W : Type*}

def attachmentWheelEmbedding (z : W) (ρ : I → V) (i : I) : W ↪ V ⊕ (I×W) where
  toFun w := if w=z then .inl (ρ i) else .inr (i,w)
  inj' := by
    intro a b hab
    by_cases ha : a=z <;> by_cases hb : b=z
    all_goals simp only [ha,hb,ite_true,ite_false,Sum.inr.injEq,Prod.mk.injEq,true_and] at hab
    · exact ha.trans hb.symm
    · cases hab
    · cases hab
    · exact hab

theorem attachmentWheelEmbedding_old (z : W) (ρ : I → V) (i : I) (w : W) (a : V) :
    attachmentWheelEmbedding z ρ i w=Sum.inl a ↔ w=z ∧ ρ i=a := by
  by_cases hw : w=z <;> simp [attachmentWheelEmbedding,hw]

theorem attachmentWheelEmbedding_private (z : W) (ρ : I → V) (i j : I) (w w' : W) :
    attachmentWheelEmbedding z ρ i w=Sum.inr (j,w') ↔ w≠z ∧ i=j ∧ w=w' := by
  by_cases hw : w=z <;> simp [attachmentWheelEmbedding,hw]

theorem attachment_cycle_no_old_edge (C : SimpleGraph W) (z : W) (ρ : I → V)
    (i : I) (a b : V) : ¬ (C.map (attachmentWheelEmbedding z ρ i)).Adj (.inl a) (.inl b) := by
  intro h
  obtain ⟨w,w',hww,ha,hb⟩ := (SimpleGraph.map_adj _ _ _ _).mp h
  have hw := (attachmentWheelEmbedding_old z ρ i w a).mp ha
  have hw' := (attachmentWheelEmbedding_old z ρ i w' b).mp hb
  exact hww.ne (hw.1.trans hw'.1.symm)

theorem attachment_cycle_old_private (C : SimpleGraph W) (z : W) (ρ : I → V)
    (i j : I) (a : V) (w : W) :
    (C.map (attachmentWheelEmbedding z ρ i)).Adj (.inl a) (.inr (j,w)) ↔
      i=j ∧ ρ i=a ∧ w≠z ∧ C.Adj z w := by
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨w₀,w₁,hC,ha,hb⟩
    have hwa := (attachmentWheelEmbedding_old z ρ i w₀ a).mp ha
    have hwz := hwa.1
    subst w₀
    obtain ⟨hw,hij,rfl⟩ := (attachmentWheelEmbedding_private z ρ i j w₁ w).mp hb
    exact ⟨hij,hwa.2,hw,hC⟩
  · rintro ⟨rfl,rfl,hw,hC⟩
    exact ⟨z,w,hC,by simp [attachmentWheelEmbedding],by simp [attachmentWheelEmbedding,hw]⟩

theorem attachment_cycle_private_private (C : SimpleGraph W) (z : W) (ρ : I → V)
    (i j k : I) (w w' : W) :
    (C.map (attachmentWheelEmbedding z ρ i)).Adj (.inr (j,w)) (.inr (k,w')) ↔
      i=j ∧ i=k ∧ w≠z ∧ w'≠z ∧ C.Adj w w' := by
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨a,b,hC,ha,hb⟩
    obtain ⟨hwa,hij,rfl⟩ := (attachmentWheelEmbedding_private z ρ i j a w).mp ha
    obtain ⟨hwb,hik,rfl⟩ := (attachmentWheelEmbedding_private z ρ i k b w').mp hb
    exact ⟨hij,hik,hwa,hwb,hC⟩
  · rintro ⟨rfl,rfl,hw,hw',hC⟩
    exact ⟨w,w',hC,by simp [attachmentWheelEmbedding,hw],by simp [attachmentWheelEmbedding,hw']⟩

def ordinaryAttachmentRim (G : SimpleGraph V) (C : SimpleGraph W) (z : W) (ρ : I → V) :
    SimpleGraph (V ⊕ (I×W)) where
  Adj a b := match a,b with
    | .inl a,.inl b => G.Adj a b
    | .inl a,.inr (i,w) => ρ i=a ∧ w≠z ∧ C.Adj z w
    | .inr (i,w),.inl a => ρ i=a ∧ w≠z ∧ C.Adj z w
    | .inr (i,w),.inr (j,w') => i=j ∧ w≠z ∧ w'≠z ∧ C.Adj w w'
  symm := ⟨by
    intro a b h
    rcases a with a|⟨i,w⟩ <;> rcases b with b|⟨j,w'⟩
    · exact h.symm
    · exact h
    · exact h
    · exact ⟨h.1.symm,h.2.2.1,h.2.1,h.2.2.2.symm⟩⟩
  loopless := ⟨by
    intro a h
    rcases a with a|⟨i,w⟩
    · exact h.ne rfl
    · exact h.2.2.2.ne rfl⟩

def ordinaryAttachmentSpokes {U : Type*} (H : V → U → Prop) (z : W) (ρ : I → V) :
    (V ⊕ (I×W)) → (U ⊕ I) → Prop
  | .inl a,.inl b => H a b
  | .inl a,.inr i => ρ i=a
  | .inr (i,w),.inl _ => False
  | .inr (i,w),.inr j => w≠z ∧ i=j

theorem ordinaryAttachmentRim_eq (G : SimpleGraph V) (C : SimpleGraph W) (z : W) (ρ : I → V) :
    ordinaryAttachmentRim G C z ρ = G.map (⟨Sum.inl,Sum.inl_injective⟩ : V ↪ V ⊕ (I×W)) ⊔
      ⨆ i,C.map (attachmentWheelEmbedding z ρ i) := by
  ext a b
  rcases a with a|⟨i,w⟩ <;> rcases b with b|⟨j,w'⟩
  all_goals simp [ordinaryAttachmentRim,SimpleGraph.sup_adj,SimpleGraph.map_adj,SimpleGraph.iSup_adj,
    attachmentWheelEmbedding_old,attachmentWheelEmbedding_private,SimpleGraph.adj_comm]
  all_goals simp only [SimpleGraph.map_adj']
  all_goals simp
  all_goals aesop

end Oberwolfach
