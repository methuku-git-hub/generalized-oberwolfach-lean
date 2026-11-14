module

public import Oberwolfach.CandidateAbsorberGroundRestriction
public import Oberwolfach.AbsorberForbiddenPairCounts

@[expose] public section

/-! Sparse pair restrictions with separate incident and nonincident
losses. No linear bound on the total number of deleted pairs is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C T:Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  [Fintype T] [DecidableEq T] {c:ℕ}

theorem candidate_absorber_ground_general_pair_loss (R:C→Finset V)
    (S:T→VertexAbsorberTemplate c) (X Y:Finset V) (J:ℕ)
    (hJ:∀ U:Finset V,Fintype.card {i:C // R i=U}≤J)
    (E:Finset (V×V)) (hE:∀ e∈E,e.1≠e.2):
    absorberGroundCount R S X Y≤
      absorberGroundCount (candidateResourceSet R
        (fun i=>∀ e:E,¬(e.val.1∈R i ∧ e.val.2∈R i))) S X Y+
      (((E.filter (fun e=>e.1∈X ∨ e.2∈X)).card*
          ((c*c)*Fintype.card T*X.card^c*Y.card^(c*c-1)*J^(2*c+1))+
        (E.filter (fun e=>¬(e.1∈X ∨ e.2∈X))).card*
          ((c*c)^2*Fintype.card T*X.card^c*Y.card^(c*c-2)*J^(2*c+1)):ℕ):ℝ):=by
  let P:=fun i=>∀ e:E,¬(e.val.1∈R i ∧ e.val.2∈R i)
  letI:DecidablePred P:=Classical.decPred P
  have hh:=candidate_absorber_ground_loss R P S X Y
  have he (D:LabelledAbsorberFamily R S X):
      (labelledAbsorberFree R (S D.1) X D.2⊆Y ∧ ¬∀ o,P (D.2.2 o).val)↔
      (labelledAbsorberFree R (S D.1) X D.2⊆Y ∧
        ∃ e∈E,∃ o,e.1∈R (D.2.2 o).val ∧ e.2∈R (D.2.2 o).val):=by
    simp only [P,not_forall,not_not,Subtype.exists];tauto
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he)] at hh
  have hb:=labelled_absorber_forbidden_pairs_count R S X Y J hJ E hE
  apply hh.trans
  convert add_le_add (le_refl (absorberGroundCount (candidateResourceSet R P) S X Y)) ((Nat.cast_le (α:=ℝ)).mpr hb) using 1 <;> congr!

end Oberwolfach
