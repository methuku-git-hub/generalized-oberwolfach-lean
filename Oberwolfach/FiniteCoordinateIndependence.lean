module

public import Oberwolfach.CommonEvents

@[expose] public section

/-! Independence of events determined by disjoint finite sets of the
original categorical coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {E : Type*} [Fintype E] [DecidableEq E]
    {State : E → Type*} [∀ e,Fintype (State e)]

theorem finiteLaw_disjoint_coordinate_events
    (μ : ∀ e,FiniteLaw (State e)) (S T : Finset E) (hST : Disjoint S T)
    (A : (∀ e : S,State e) → Prop) (B : (∀ e : T,State e) → Prop) :
    (FiniteLaw.pi μ).probability (fun σ=>A (fun e : S=>σ e) ∧ B (fun e : T=>σ e))=
      (FiniteLaw.pi μ).probability (fun σ=>A (fun e : S=>σ e))*
        (FiniteLaw.pi μ).probability (fun σ=>B (fun e : T=>σ e)) := by
  let : ∀ e,MeasurableSpace (State e) := fun _=>⊤
  let : ∀ e,MeasurableSingletonClass (State e) := fun _=>⟨fun _=>trivial⟩
  have hcoord : iIndepFun (fun (e : E) (σ : ∀ i,State i)=>σ e) (FiniteLaw.pi μ).toPMF.toMeasure := by
    rw [finiteLaw_pi_measure]
    exact iIndepFun_pi (fun _=>aemeasurable_id)
  have hh := hcoord.indepFun_finset S T hST (fun e=>measurable_pi_apply e)
  have hm := hh.measure_inter_preimage_eq_mul {σ | A σ} {σ | B σ}
    (Set.toFinite _).measurableSet (Set.toFinite _).measurableSet
  have hr := congrArg ENNReal.toReal hm
  rw [ENNReal.toReal_mul] at hr
  change (FiniteLaw.pi μ).toPMF.toMeasure.real
      {σ | A (fun e : S=>σ e) ∧ B (fun e : T=>σ e)} =
    (FiniteLaw.pi μ).toPMF.toMeasure.real {σ | A (fun e : S=>σ e)} *
      (FiniteLaw.pi μ).toPMF.toMeasure.real {σ | B (fun e : T=>σ e)} at hr
  simpa only [finiteLaw_probability_measure] using hr

theorem finiteLaw_disjoint_supported_events
    (μ : ∀ e,FiniteLaw (State e)) (S T : Finset E) (hST : Disjoint S T)
    (A B : (∀ e,State e) → Prop)
    (hA : ∀ σ τ,(∀ e∈S,σ e=τ e) → (A σ ↔ A τ))
    (hB : ∀ σ τ,(∀ e∈T,σ e=τ e) → (B σ ↔ B τ)) :
    (FiniteLaw.pi μ).probability (fun σ=>A σ ∧ B σ)=
      (FiniteLaw.pi μ).probability A*(FiniteLaw.pi μ).probability B := by
  let extend (U : Finset E) (τ : ∀ e : U,State e) (e : E) : State e :=
    if he : e∈U then τ ⟨e,he⟩ else Classical.choice (finiteLaw_nonempty (μ e))
  have hext (U : Finset E) (σ : ∀ e,State e) (e : E) (he : e∈U) :
      σ e=extend U (fun e : U=>σ e) e := by simp only [extend,dif_pos he]
  have ha (σ : ∀ e,State e) : A (extend S (fun e : S=>σ e)) ↔ A σ :=
    (hA σ _ (hext S σ)).symm
  have hb (σ : ∀ e,State e) : B (extend T (fun e : T=>σ e)) ↔ B σ :=
    (hB σ _ (hext T σ)).symm
  have hh := finiteLaw_disjoint_coordinate_events μ S T hST (fun τ=>A (extend S τ))
    (fun τ=>B (extend T τ))
  simpa only [ha,hb] using hh

end Oberwolfach
