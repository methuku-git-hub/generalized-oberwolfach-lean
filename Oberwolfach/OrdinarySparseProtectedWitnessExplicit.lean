module

public import Oberwolfach.SparseOrdinaryCorrectionExplicit
public import Oberwolfach.OrdinarySparseCorrectionAtOrder
public import Oberwolfach.OrdinaryProtectedCorrectionRealization

@[expose] public section
/-! The uniform sparse-correction lemma supplies the protected-rectangle
    witness at the selected order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_sparse_protected_rectangle_witness_explicit
    (r:ℕ) (hr:3≤r) (ω h δ ξ:ℝ)
    (hω:0<ω) (hh:0<h) (hδ:0<δ) (hδsmall:δ<1/4)
    (hξ:0<ξ) (hξh:ξ≤h/100)
    : ∃n₀:ℕ,∀(η:ℝ),0≤η→η≤δ*ω*ξ/1000→
    ∀(V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
    n₀≤Fintype.card V→
    ∀(hωn:ω*Fintype.card V≤Fintype.card U) (hUn:Fintype.card U≤Fintype.card V)
    (Q:SimpleGraph V) (H:V→U→Prop) (R:V→V→Prop) (T:Finset V) (B:Finset U)
    (hbal:∀v,|(Q.degree v:ℝ)-2*(Finset.univ.filter (H v)).card|≤η*Fintype.card V),
(∀x y,relationMultiplicity (fun x y=>R x y ∧ ¬(x∈T ∧ y∈T)) x y+
        relationMultiplicity (fun x y=>R x y ∧ ¬(x∈T ∧ y∈T)) y x=
          if (Q\spanningRestriction Q T).Adj x y then 1 else 0) →
      BipartiteLargeCut (relationMultiplicity (fun x y=>R x y ∧ ¬(x∈T ∧ y∈T))) δ h →
      BipartiteLargeCut (relationMultiplicity (fun v u=>H v u ∧ ¬(v∈T ∧ u∈B))) δ h →
      ∃(JQ:SimpleGraph V) (JH:V→U→Prop),
        JQ≤Q\spanningRestriction Q T ∧ (∀v u,JH v u→H v u ∧ ¬(v∈T ∧ u∈B)) ∧
        (∀v,(Q\JQ).degree v=2*(Finset.univ.filter (fun u=>H v u ∧ ¬JH v u)).card) ∧
        (∀u,r∣(Finset.univ.filter (fun v=>H v u ∧ ¬JH v u)).card) ∧
        (∀v,(JQ.degree v:ℝ)+(Finset.univ.filter (JH v)).card≤10*ξ*Fintype.card V) ∧
        (∀u,((Finset.univ.filter (fun v=>JH v u)).card:ℝ)≤10*ξ*Fintype.card V) :=by
  obtain ⟨n₀,hmain⟩:=sparse_ordinary_degree_correction_explicit r hr ω h δ ξ hω hh hδ hδsmall hξ hξh
  refine ⟨n₀,?_⟩
  intro η hη hηsmall V U _ _ _ _ hn hωn hUn Q H R T B hbal ho hcR hcH
  have hmat:relationMultiplicity (fun v u=>H v u ∧ ¬(v∈T ∧ u∈B)) =
      (fun v u=>if H v u ∧ ¬((fun v u=>v∈T ∧ u∈B) v u) then 1 else 0):=by
    funext v u
    unfold relationMultiplicity
    split_ifs <;> rfl
  apply hmain η hη hηsmall V U hn hωn hUn
    Q (spanningRestriction Q T) H (fun v u=>v∈T ∧ u∈B)
    (relationMultiplicity (fun x y=>R x y ∧ ¬(x∈T ∧ y∈T))) ho hcR
  · rw [hmat] at hcH
    convert hcH using 1 <;> congr! 5 <;> exact Subsingleton.elim _ _
  · exact hbal
end Oberwolfach
