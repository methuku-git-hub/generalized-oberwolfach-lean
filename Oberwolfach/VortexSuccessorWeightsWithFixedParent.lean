module

public import Oberwolfach.SuccessorWeightsPreserveParent
public import Oberwolfach.VortexFullSuccessorWeightFamilies
public import Oberwolfach.VortexMarkedParentDegrees
public import Oberwolfach.SuccessorWeightFamilies
public import Oberwolfach.MarkedPhysicalDeletionRestriction

@[expose] public section

/-! Actual full vortex domains admit the separated positive successor
weights used in marked completion. All weights are chosen from the parent
graphs and permutations before any sampling marginals or outcomes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem vortex_full_successor_weight_families_with_fixed_parent
    (k c : ℕ) (hlen : c+1=(k+2)*2) (α τ : ℝ) (hα : 0<α) (hτ : 0<τ)
    (hmargin : successorCycleRatio k+α/4≤1/2+α/2) :
    ∃ βmax : ℝ,0<βmax ∧ ∀ b : ℕ,∃ N : ℕ,1≤ N ∧
    ∀ (V U : Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G : SimpleGraph V) (D m : ℕ) (β ε : ℝ) (Q : Vortex U G D β ε m),
    G.IsRegularOfDegree D → 0< Fintype.card V →
    (1/2+α)*Fintype.card V≤(D:ℝ) → 0< initialIndexDensity U D →
    0≤β → β≤βmax → 0<ε → ε≤1/4 → (N:ℝ)≤ε*m/2 →
    let A := fun i=>Q.vertices i
    let B := fun i=>Q.indices i;
    ∀ ρ : ∀ i,Equiv.Perm (A i),
    ∀ parent:(Fin (c+1)→A 0)→ℝ,
      SuccessorSequenceWeightConditions (G.comap (Subtype.val:A 0→V)) (ρ 0) b
        (2*(B 0).card/initialIndexDensity U D) τ (successorWeightLower k (α/4)) (successorWeightUpper k (α/4)) parent →
    ∃ weight : ∀ i,(Fin (c+1)→A i)→ℝ,weight 0=parent ∧
      (∀ i≤ Q.length,SuccessorSequenceWeightConditions
        (G.comap (Subtype.val : A i→V)) (ρ i) b (2*(B i).card/initialIndexDensity U D) τ
        (successorWeightLower k (α/4)) (successorWeightUpper k (α/4)) (weight i)) := by
  obtain ⟨βmax,hβmax,hbase⟩:=vortex_full_successor_weight_families k c hlen α τ hα hτ hmargin
  refine ⟨βmax,hβmax,?_⟩
  intro b
  obtain ⟨N,hN,hbase⟩:=hbase b
  refine ⟨N,hN,?_⟩
  intro V U _ _ _ _ G D m β ε Q hreg hn hD hρ hb hbmax he he1 hsize A B ρ parent hparent
  obtain ⟨weight,hw⟩:=hbase V U G D m β ε Q hreg hn hD hρ hb hbmax he he1 hsize ρ
  obtain ⟨updated,hzero,_,hupdated⟩:=successor_weight_family_preserve_parent (fun i=>A i) c b
    (fun i=>G.comap (Subtype.val:A i→V)) ρ (fun i=>2*(B i).card/initialIndexDensity U D)
    τ (successorWeightLower k (α/4)) (successorWeightUpper k (α/4)) Q.length weight hw parent hparent
  exact ⟨updated,hzero,hupdated⟩
end Oberwolfach
