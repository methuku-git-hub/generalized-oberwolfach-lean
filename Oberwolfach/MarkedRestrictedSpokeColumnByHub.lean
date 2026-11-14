module

public import Oberwolfach.MarkedRestrictedSpokeColumnBounds

@[expose] public section
/-! Inner hubs have exact ordinary-spoke agreement; the remaining hubs use
the local gain and loss bounds on the same protected vertex set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_restricted_spoke_column_bounds_by_hub
    {V W U Z:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
    [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]
    (f:W↪V) (g:Z→U) (A:Finset V) (hf:∀x,f x∈A) (inner:Finset U)
    (H H':Bool→V→U→Prop) (hmark:∀x u,H true x u↔H' true x u)
    (loss gain:ℝ) (hloss:0≤loss) (hgain:0≤gain)
    (hexact:∀u∈inner,∀x∈A,H false x u↔H' false x u)
    (hLoss:∀u∉inner,((A.filter (fun x=>H false x u∧¬H' false x u)).card:ℝ)≤loss)
    (hGain:∀u∉inner,((A.filter (fun x=>H' false x u∧¬H false x u)).card:ℝ)≤gain):
    let HL:=fun b x u=>H b (f x) (g u)
    let HL':=fun b x u=>H' b (f x) (g u);
    ∀u:Z,((markedSpokeChangeGraph HL HL').degree (Sum.inr u):ℝ)≤loss+gain :=by
  intro HL HL'
  have hLossAll:∀u,((A.filter (fun x=>H false x u∧¬H' false x u)).card:ℝ)≤loss:=by
    intro u
    by_cases hu:u∈inner
    · have hempty:A.filter (fun x=>H false x u∧¬H' false x u)=∅:=by
        ext x
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hx,h,h'⟩
          exact False.elim (h' ((hexact u hu x hx).mp h))
        · intro hx
          simpa using hx
      rw [hempty]
      simpa using hloss
    · exact hLoss u hu
  have hGainAll:∀u,((A.filter (fun x=>H' false x u∧¬H false x u)).card:ℝ)≤gain:=by
    intro u
    by_cases hu:u∈inner
    · have hempty:A.filter (fun x=>H' false x u∧¬H false x u)=∅:=by
        ext x
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hx,h,h'⟩
          exact False.elim (h' ((hexact u hu x hx).mpr h))
        · intro hx
          simpa using hx
      rw [hempty]
      simpa using hgain
    · exact hGain u hu
  exact marked_restricted_spoke_column_bounds f g A hf H H' hmark loss gain hLossAll hGainAll
end Oberwolfach
