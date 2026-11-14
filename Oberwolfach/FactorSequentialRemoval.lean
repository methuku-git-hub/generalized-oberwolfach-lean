module

public import Oberwolfach.GraphDeletion
public import Oberwolfach.Definitions

@[expose] public section
/-! Sequentially remove finitely many prescribed factors, conditional only on
the indicated single-copy existence result. The residual degree and physical
edge partition are tracked exactly. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_sequential_removal {n:ℕ} (T D:ℕ)
    (G:SimpleGraph (Fin n)) (hG:G.IsRegularOfDegree D)
    (F:List (SimpleGraph (Fin n))) (hmargin:T+2*F.length≤D)
    (hcopy:∀ P:SimpleGraph (Fin n),∀ d:ℕ, P.IsRegularOfDegree d→T≤d→
      ∀ A∈F,∃ H:SimpleGraph (Fin n),H≤P ∧ H.IsRegularOfDegree 2 ∧ Nonempty (H ≃g A)):
    ∃ R:SimpleGraph (Fin n),∃ pieces:List (SimpleGraph (Fin n)),
      R.IsRegularOfDegree (D-2*F.length) ∧ R≤G ∧
      List.Forall₂ (fun H A=>Nonempty (H ≃g A) ∧ H.IsRegularOfDegree 2) pieces F ∧
      (∀ H∈pieces,H≤G ∧ ∀ u v,H.Adj u v→¬R.Adj u v) ∧
      pieces.Pairwise (fun H J=>∀ u v,H.Adj u v→¬J.Adj u v) ∧
      (∀ u v,G.Adj u v ↔ R.Adj u v ∨ ∃ H∈pieces,H.Adj u v):=by
  induction F generalizing G D with
  | nil =>
    refine ⟨G,[],?_,le_rfl,?_,?_,?_,?_⟩
    · simpa using hG
    · exact List.Forall₂.nil
    · simp
    · simp
    · intro u v
      simp
  | cons A F ih =>
    have hlen:T+2*(F.length+1)≤D:=by simpa using hmargin
    have hT:T≤D:=by omega
    obtain ⟨H,hHP,hH,hIso⟩:=hcopy G D hG hT A (by simp)
    let P:SimpleGraph (Fin n):=G\H
    letI : DecidableRel P.Adj := Classical.decRel _
    have hrem:P.IsRegularOfDegree (D-2):=by
      intro v
      change (G\H).degree v=D-2
      have hh:=graph_degree_sdiff G H hHP v
      rw [hG v,hH v] at hh
      convert hh using 1
      unfold SimpleGraph.degree
      congr 1
      ext y
      simp only [SimpleGraph.mem_neighborFinset]
    have hsd:G\H≤G:=sdiff_le
    have hmargin':T+2*F.length≤D-2:=by omega
    have hcopy':∀ P:SimpleGraph (Fin n),∀ d:ℕ,P.IsRegularOfDegree d→T≤d→
        ∀ A∈F,∃ J:SimpleGraph (Fin n),J≤P ∧ J.IsRegularOfDegree 2 ∧ Nonempty (J ≃g A):=by
      intro P d hp hd A hA
      exact hcopy P d hp hd A (by simp [hA])
    obtain ⟨R,pieces,hR,hRG,hrel,hpiece,hpair,hexact⟩:=ih (D-2) P hrem hmargin' hcopy'
    refine ⟨R,H::pieces,?_,hRG.trans (sdiff_le),List.Forall₂.cons ⟨hIso,hH⟩ hrel,?_,?_,?_⟩
    · convert hR using 1 <;> simp only [List.length_cons] <;> omega
    · intro J hJ
      rcases List.mem_cons.mp hJ with rfl | hJ
      · refine ⟨hHP,?_⟩
        intro u v huv hrv
        exact ((hRG hrv).2 huv)
      · obtain ⟨hJP,hJR⟩:=hpiece J hJ
        exact ⟨hJP.trans sdiff_le,hJR⟩
    · apply List.Pairwise.cons
      · intro J hJ u v huv hjv
        have hJP: J≤G\H:=(hpiece J hJ).1
        exact ((hJP hjv).2 huv)
      · exact hpair
    · intro u v
      constructor
      · intro huv
        by_cases h: H.Adj u v
        · exact Or.inr ⟨H,by simp,h⟩
        · have hrest:(G\H).Adj u v:=⟨huv,h⟩
          rcases (hexact u v).1 hrest with hR | ⟨J,hJ,hj⟩
          · exact Or.inl hR
          · exact Or.inr ⟨J,by simp [hJ],hj⟩
      · rintro (hR | ⟨J,hJ,hj⟩)
        · exact hsd (hRG hR)
        · rcases List.mem_cons.mp hJ with rfl | hJ
          · exact hHP hj
          · exact hsd ((hpiece J hJ).1 hj)
end Oberwolfach
