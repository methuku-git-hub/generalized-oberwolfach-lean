module

public import Oberwolfach.MarkedSpokeColumnFromLossAndGain

@[expose] public section
/-! Local one-sided bounds on the first inner set restrict to its first
active subset without losing a factor of the ambient host size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_restricted_spoke_column_bounds
    {V W U Z:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
    [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]
    (f:W↪V) (g:Z→U) (A:Finset V) (hf:∀x,f x∈A)
    (H H':Bool→V→U→Prop) (hmark:∀x u,H true x u↔H' true x u)
    (loss gain:ℝ)
    (hLoss:∀u,((A.filter (fun x=>H false x u∧¬H' false x u)).card:ℝ)≤loss)
    (hGain:∀u,((A.filter (fun x=>H' false x u∧¬H false x u)).card:ℝ)≤gain):
    let HL:=fun b x u=>H b (f x) (g u)
    let HL':=fun b x u=>H' b (f x) (g u);
    ∀u:Z,((markedSpokeChangeGraph HL HL').degree (Sum.inr u):ℝ)≤loss+gain :=by
  intro HL HL'
  have hcard (pred:V→Prop):
      (Finset.univ.filter (fun x:W=>pred (f x))).card≤(A.filter pred).card:=by
    have himage:(Finset.univ.filter (fun x:W=>pred (f x))).image f⊆A.filter pred:=by
      intro y hy
      obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hy
      exact Finset.mem_filter.mpr ⟨hf x,(Finset.mem_filter.mp hx).2⟩
    rw [←Finset.card_image_of_injective _ f.injective]
    exact Finset.card_le_card himage
  apply marked_spoke_column_from_loss_and_gain HL HL'
    (fun x u=>hmark (f x) (g u)) loss gain
  · intro u
    have hh:=hcard (fun x=>H false x (g u)∧¬H' false x (g u))
    have hh':((Finset.univ.filter (fun x:W=>HL false x u∧¬HL' false x u)).card:ℝ)≤
        ((A.filter (fun x=>H false x (g u)∧¬H' false x (g u))).card:ℝ):=by
      change ((Finset.univ.filter (fun x:W=>H false (f x) (g u)∧¬H' false (f x) (g u))).card:ℝ) ≤ _
      have hnat:(Finset.univ.filter (fun x:W=>H false (f x) (g u)∧¬H' false (f x) (g u))).card ≤
          (A.filter (fun x=>H false x (g u)∧¬H' false x (g u))).card :=by
        convert hh using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
      exact_mod_cast hnat
    exact hh'.trans (hLoss (g u))
  · intro u
    have hh:=hcard (fun x=>H' false x (g u)∧¬H false x (g u))
    have hh':((Finset.univ.filter (fun x:W=>HL' false x u∧¬HL false x u)).card:ℝ)≤
        ((A.filter (fun x=>H' false x (g u)∧¬H false x (g u))).card:ℝ):=by
      change ((Finset.univ.filter (fun x:W=>H' false (f x) (g u)∧¬H false (f x) (g u))).card:ℝ) ≤ _
      have hnat:(Finset.univ.filter (fun x:W=>H' false (f x) (g u)∧¬H false (f x) (g u))).card ≤
          (A.filter (fun x=>H' false x (g u)∧¬H false x (g u))).card :=by
        convert hh using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
      exact_mod_cast hnat
    exact hh'.trans (hGain (g u))
end Oberwolfach
