module

public import Oberwolfach.OrdinaryLocalDeletionCandidates
public import Oberwolfach.CandidateAbsorberVertexLoss
public import Oberwolfach.CandidateAbsorberPairLoss

@[expose] public section

/-! The original labelled absorber count supplies the count after both
row and rim deletions. No cycle, root map or template is reweighted. -/
set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V Tpl : Type} [Fintype V] [DecidableEq V] [Fintype Tpl] [DecidableEq Tpl] {r : ℕ}

def ordinaryAbsorberDeletionCoefficient (r N : ℕ) : ℕ :=
  ((r*r)+(r*r)^2)*N*r^r*(r^r)^(2*r+1)

theorem ordinary_restricted_profile_absorbers (Q D F : SimpleGraph V) (T Z X : Finset V)
    (hr : 2≤r) (hn : 1≤Fintype.card V) (hX : X.card=r) (hXZ : Disjoint X Z)
    (S : Tpl → VertexAbsorberTemplate r) :
    Fintype.card (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q) (F:=F) (T:=T) (r:=r)) S X)≤
      Fintype.card (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q\D) (F:=F) (T:=T\Z) (r:=r)) S X)+
      (Z.card+D.edgeFinset.card)*ordinaryAbsorberDeletionCoefficient r (Fintype.card Tpl)*
        (Fintype.card V)^(r*r-1) := by
  let R := localOrdinaryVertices (Q:=Q) (F:=F) (T:=T) (r:=r)
  let P := fun C=>Disjoint (R C) Z
  let R' := candidateResourceSet R P
  let E := canonicalGraphPairs D
  let P' := fun C : {C // P C}=>∀ e:E,¬(e.val.1∈R' C ∧ e.val.2∈R' C)
  let R'' := candidateResourceSet R' P'
  have hJ := local_ordinary_multiplicity (r:=r) Q F T
  have hJ' := candidate_resource_multiplicity R P (r^r) hJ
  have hv := candidate_absorber_vertex_loss R S X Z hXZ (r^r) hJ
  have he := candidate_absorber_pair_loss hr hn R' S X (r^r) hJ' E
    (fun e he=>(canonicalGraphPairs_adj D e he).ne)
  have hlift : Fintype.card (LabelledAbsorberFamily R'' S X)≤
      Fintype.card (LabelledAbsorberFamily (localOrdinaryVertices (Q:=Q\D) (F:=F) (T:=T\Z) (r:=r)) S X) := by
    exact absorber_family_card_embedding R'' localOrdinaryVertices
      (localOrdinaryRetainedEmbedding (r:=r) Q D F T Z) (fun _=>rfl) S X
  rw [hX] at hv he
  change Fintype.card (LabelledAbsorberFamily R' S X)≤Fintype.card (LabelledAbsorberFamily R'' S X)+_ at he
  have hE : E.card=D.edgeFinset.card := canonicalGraphPairs_card D
  rw [hE] at he
  have hc : (r*r)*Fintype.card Tpl*r^r*(Fintype.card V)^(r*r-1)*(r^r)^(2*r+1)≤
      ordinaryAbsorberDeletionCoefficient r (Fintype.card Tpl)*(Fintype.card V)^(r*r-1) := by
    dsimp [ordinaryAbsorberDeletionCoefficient]
    nlinarith only [Nat.zero_le ((r*r)^2*Fintype.card Tpl*r^r*(Fintype.card V)^(r*r-1)*(r^r)^(2*r+1))]
  have heq : ((r*r)+(r*r)^2)*Fintype.card Tpl*r^r*(Fintype.card V)^(r*r-1)*(r^r)^(2*r+1)=
      ordinaryAbsorberDeletionCoefficient r (Fintype.card Tpl)*(Fintype.card V)^(r*r-1) := by
    dsimp [ordinaryAbsorberDeletionCoefficient];ring
  rw [heq] at he
  have hv' := hv.trans (Nat.add_le_add_left (Nat.mul_le_mul_left Z.card hc) _)
  change Fintype.card (LabelledAbsorberFamily R S X)≤_
  nlinarith only [hv',he,hlift]

end Oberwolfach
