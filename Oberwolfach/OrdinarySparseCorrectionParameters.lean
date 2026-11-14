module

public import Oberwolfach.SparseOrdinaryCorrection

@[expose] public section
/-! Name the uniform sparse-correction parameters before the host order and
vertex types are chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinarySparseCorrectionParameters
    (r:ℕ) (hr:3≤r) (ω h δ ξ:ℝ)
    (hω:0<ω) (hh:0<h) (hδ:0<δ) (hδsmall:δ<1/4)
    (hξ:0<ξ) (hξh:ξ≤h/100):ℝ×ℕ:=
  let hex:=sparse_ordinary_degree_correction.{0,0} r hr ω h δ ξ hω hh hδ hδsmall hξ hξh
  ⟨Classical.choose hex,Classical.choose (Classical.choose_spec hex).2⟩

theorem ordinary_sparse_correction_parameters_spec
    (r:ℕ) (hr:3≤r) (ω h δ ξ:ℝ)
    (hω:0<ω) (hh:0<h) (hδ:0<δ) (hδsmall:δ<1/4)
    (hξ:0<ξ) (hξh:ξ≤h/100):
    let p:=ordinarySparseCorrectionParameters r hr ω h δ ξ hω hh hδ hδsmall hξ hξh;
    0<p.1 ∧ ∀η:ℝ,0≤η→η≤p.1→
      ∀(V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      p.2≤Fintype.card V → ω*Fintype.card V≤Fintype.card U → Fintype.card U≤Fintype.card V →
      ∀(Q FQ:SimpleGraph V) (H FH:V→U→Prop) (A:V→V→ℕ),
      (∀x y,A x y+A y x=if (Q\FQ).Adj x y then 1 else 0) →
      BipartiteLargeCut A δ h →
      BipartiteLargeCut (fun v u=>if H v u ∧ ¬FH v u then 1 else 0) δ h →
      (∀v,|(Q.degree v:ℝ)-2*(Finset.univ.filter (H v)).card|≤η*Fintype.card V) →
      ∃(JQ:SimpleGraph V) (JH:V→U→Prop),
        JQ≤Q\FQ ∧ (∀v u,JH v u→H v u ∧ ¬FH v u) ∧
        (∀v,(Q\JQ).degree v=2*(Finset.univ.filter (fun u=>H v u ∧ ¬JH v u)).card) ∧
        (∀u,r∣(Finset.univ.filter (fun v=>H v u ∧ ¬JH v u)).card) ∧
        (∀v,(JQ.degree v:ℝ)+(Finset.univ.filter (JH v)).card≤10*ξ*Fintype.card V) ∧
        (∀u,((Finset.univ.filter (fun v=>JH v u)).card:ℝ)≤10*ξ*Fintype.card V):=by
  intro p
  have hex:=sparse_ordinary_degree_correction.{0,0} r hr ω h δ ξ hω hh hδ hδsmall hξ hξh
  exact ⟨(Classical.choose_spec hex).1,Classical.choose_spec (Classical.choose_spec hex).2⟩
end Oberwolfach
