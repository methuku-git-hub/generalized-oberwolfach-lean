module

public import Oberwolfach.OrdinarySparseCorrectionParameters

@[expose] public section
/-! Instantiate the uniform correction parameters after the host order and
    forbidden graphs are known. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_sparse_correction_at_order
    (r:ℕ) (hr:3≤r) (ω h δ ξ:ℝ)
    (hω:0<ω) (hh:0<h) (hδ:0<δ) (hδsmall:δ<1/4)
    (hξ:0<ξ) (hξh:ξ≤h/100)
    (η:ℝ) (hη:0≤η)
    (hηsmall:η≤(ordinarySparseCorrectionParameters r hr ω h δ ξ hω hh hδ hδsmall hξ hξh).1)
    (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (hn:(ordinarySparseCorrectionParameters r hr ω h δ ξ hω hh hδ hδsmall hξ hξh).2≤Fintype.card V)
    (hωn:ω*Fintype.card V≤Fintype.card U) (hUn:Fintype.card U≤Fintype.card V)
    (Q FQ:SimpleGraph V) (H FH:V→U→Prop) (A:V→V→ℕ)
    (hOrient:∀x y,A x y+A y x=if (Q\FQ).Adj x y then 1 else 0)
    (hcutR:BipartiteLargeCut A δ h)
    (hcutH:BipartiteLargeCut (fun v u=>if H v u ∧ ¬FH v u then 1 else 0) δ h)
    (hbal:∀v,|(Q.degree v:ℝ)-2*(Finset.univ.filter (H v)).card|≤η*Fintype.card V):
    ∃(JQ:SimpleGraph V) (JH:V→U→Prop),
      JQ≤Q\FQ ∧ (∀v u,JH v u→H v u ∧ ¬FH v u) ∧
      (∀v,(Q\JQ).degree v=2*(Finset.univ.filter (fun u=>H v u ∧ ¬JH v u)).card) ∧
      (∀u,r∣(Finset.univ.filter (fun v=>H v u ∧ ¬JH v u)).card) ∧
      (∀v,(JQ.degree v:ℝ)+(Finset.univ.filter (JH v)).card≤10*ξ*Fintype.card V) ∧
      (∀u,((Finset.univ.filter (fun v=>JH v u)).card:ℝ)≤10*ξ*Fintype.card V):=by
  exact (ordinary_sparse_correction_parameters_spec r hr ω h δ ξ hω hh hδ hδsmall hξ hξh).2
    η hη hηsmall V U hn hωn hUn Q FQ H FH A hOrient hcutR hcutH hbal
end Oberwolfach
