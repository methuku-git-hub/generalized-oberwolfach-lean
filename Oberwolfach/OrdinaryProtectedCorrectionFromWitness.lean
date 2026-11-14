module

public import Oberwolfach.OrdinaryProtectedCorrectionRealization

@[expose] public section
/-! Assemble the protected cuts and a sparse correction witness without
    expanding the uniform parameter choice inside a large wrapper. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_protected_correction_from_witness
    (r:ℕ) (ξ δ h ζ:ℝ) (Q:SimpleGraph V) (H:V→U→Prop) (R:V→V→Prop) (T:Finset V) (B:Finset U)
    (hn:0<Fintype.card V) (hu:0<Fintype.card U)
    (hζ:0≤ζ) (hζh:ζ≤h) (hT:(T.card:ℝ)≤ζ*Fintype.card V) (hB:(B.card:ℝ)≤ζ*Fintype.card U)
    (hOrient:∀x y,relationMultiplicity R x y+relationMultiplicity R y x=if Q.Adj x y then 1 else 0)
    (hcutR:BipartiteLargeCut (relationMultiplicity R) δ (2*h))
    (hcutH:BipartiteLargeCut (relationMultiplicity H) δ (2*h))
    (hCorrection:
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
        (∀u,((Finset.univ.filter (fun v=>JH v u)).card:ℝ)≤10*ξ*Fintype.card V)):
    ∃(JQ:SimpleGraph V) (JH:V→U→Prop),
      JQ≤Q ∧ (∀v∈T,∀w∈T,¬JQ.Adj v w) ∧
      (∀v u,JH v u→H v u ∧ ¬(v∈T ∧ u∈B)) ∧
      (∀v,(Q\JQ).degree v=2*(Finset.univ.filter (fun u=>H v u ∧ ¬JH v u)).card) ∧
      (∀u,r∣(Finset.univ.filter (fun v=>H v u ∧ ¬JH v u)).card) ∧
      (∀v,(JQ.degree v:ℝ)+(Finset.univ.filter (JH v)).card≤10*ξ*Fintype.card V) ∧
      (∀u,((Finset.univ.filter (fun v=>JH v u)).card:ℝ)≤10*ξ*Fintype.card V):=by
  obtain ⟨ho,hr,hs⟩:=ordinary_protected_correction_cut_inputs hn hu Q H R T B δ h ζ hζ hζh hT hB hOrient hcutR hcutH
  obtain ⟨JQ,JH,hJQ,hJH,hbal,hdiv,hrow,hcol⟩:=hCorrection ho hr hs
  exact ⟨JQ,JH,ordinary_protected_correction_realization r ξ Q H T B JQ JH hJQ hJH hbal hdiv hrow hcol⟩
end Oberwolfach
