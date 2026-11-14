module

public import Oberwolfach.MarkedRetainedArcRelabel
public import Oberwolfach.OccurrenceDegreeEquivRelabel

@[expose] public section
/-! At a full-domain relabelling, the four marked rim degree estimates
are the same estimates on the original host. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [Nonempty V] [Nonempty W]
  [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_retained_arc_degrees_relabel
    (F:W↪oV) (f:W≃V) (hf:∀w,f w=F w) (g:Z≃U)
    (π:Equiv.Perm V) (ρ:Equiv.Perm W) (hc:∀w,f (ρ w)=π (f w))
    (P:SimpleGraph V) (d:ℕ) (a:Γ)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a) (mark:Bool):
    let E:=MarkedSampleArc (P.comap F) ρ (3*d)
      (fun e=>(markedRetainedPairRestriction f g π ρ hc d a z).1 (Sum.inl e)) mark
    let E':=MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) mark;
    ∀x:W,occurrenceDegree (fun e:E=>e.val.1) x=occurrenceDegree (fun e:E'=>e.val.1) (f x) ∧
      occurrenceDegree (fun e:E=>e.val.2) x=occurrenceDegree (fun e:E'=>e.val.2) (f x):=by
  intro E E' x
  let e:=markedRetainedSampleArcEquiv F f hf g π ρ hc P d a z mark
  constructor
  · exact occurrence_degree_equiv_relabel f e (fun a:E=>a.val.1) (fun a:E'=>a.val.1) (fun _=>rfl) x
  · exact occurrence_degree_equiv_relabel f e (fun a:E=>a.val.2) (fun a:E'=>a.val.2) (fun _=>rfl) x
end Oberwolfach
