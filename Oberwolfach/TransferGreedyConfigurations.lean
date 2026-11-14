module

public import Oberwolfach.TransferCyclePositions
public import Oberwolfach.TransferPositionEquivalence
public import Oberwolfach.OrdinaryTransferConfigurations

@[expose] public section

/-! Converting the counted ordered embeddings to the exact labelled
transfer configurations used by the wheel-weight construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type*} [DecidableEq V] (P F : SimpleGraph V) (A : Finset V)
    (r : ℕ) (hr : 3 ≤ r) (v : V) (f : Fin (r^2) → V)
    (hf : RootedPatternGood P F A (transferConstructionGraph r hr) v f)

def transferLabelsOfPattern : (Fin r×Fin r) ↪ V where
  toFun a := Fin.cons (α:=fun _=>V) v f (transferFullPosition r hr a)
  inj' := hf.1.comp (transferFullPosition_injective r hr)

theorem transferLabelsOfPattern_apply (a : Fin r×Fin r) :
    transferLabelsOfPattern P F A r hr v f hf a=f (transferFreePosition r hr a) := by
  simp only [transferLabelsOfPattern,Function.Embedding.coeFn_mk,transferFullPosition,Fin.cons_succ]

theorem transferLabelsOfPattern_omitted : v∉Set.range (transferLabelsOfPattern P F A r hr v f hf) := by
  rintro ⟨a,ha⟩
  have he : Fin.cons (α:=fun _=>V) v f (transferFullPosition r hr a)=Fin.cons (α:=fun _=>V) v f 0 := by
    simpa only [Fin.cons_zero,transferLabelsOfPattern,Function.Embedding.coeFn_mk] using ha
  have hh := congrArg Fin.val (hf.1 he)
  change ((transferFreePosition r hr a).val+1)=0 at hh
  omega

def transferRowFullPosition (i : Fin r) (rooted : Bool) (j : Fin r) : Fin (r^2+1) :=
  if rooted=true ∧ (j:ℕ)=0 then 0 else transferFullPosition r hr (i,j)

theorem transferRowFullPosition_val (i : Fin r) (rooted : Bool) (j : Fin r) :
    (transferRowFullPosition r hr i rooted j:ℕ)=
      transferCyclePosition r i (if rooted then 0 else (i:ℕ)+1) j := by
  cases rooted <;> by_cases hj : (j:ℕ)=0 <;>
    simp [transferRowFullPosition,transferCyclePosition,hj,transferFullPosition_val,transferVertexPosition]

theorem transferLabelsOfPattern_rim (idx : TransferCycleIndex r) :
    transferCycleGraph (by omega) (transferLabelsOfPattern P F A r hr v f hf) v
      (transferLabelsOfPattern_omitted P F A r hr v f hf) idx≤P := by
  let labels := transferLabelsOfPattern P F A r hr v f hf
  let g : Fin (r^2+1) → V := Fin.cons v f
  rcases idx with ⟨⟩|⟨i,b⟩
  · intro z w hzw
    simp only [transferCycleGraph] at hzw
    rw [SimpleGraph.map_adj] at hzw
    obtain ⟨a,b,hab,rfl,rfl⟩ := hzw
    apply hf.2.2.2 (transferFullPosition r hr (a,⟨0,by omega⟩))
      (transferFullPosition r hr (b,⟨0,by omega⟩))
    simpa only [transferFullPosition_val,transferVertexPosition,ite_true] using
      transferConstructionGraph_base_cycle r hr a b hab
  · have heval (j : Fin r) :
        g (transferRowFullPosition r hr i b j)=
          (if b then transferRootedEmbedding (by omega) labels v
            (transferLabelsOfPattern_omitted P F A r hr v f hf) i else transferRowEmbedding labels i) j := by
      cases b <;> by_cases hj : (j:ℕ)=0 <;>
        simp [transferRowFullPosition,transferRootedEmbedding,transferRowEmbedding,
          labels,transferLabelsOfPattern,g,Fin.ext_iff,hj]
    have hgraph : transferCycleGraph (by omega) labels v
        (transferLabelsOfPattern_omitted P F A r hr v f hf) (Sum.inr (i,b))=
      (SimpleGraph.cycleGraph r).map
        ((if b then transferRootedEmbedding (by omega) labels v
          (transferLabelsOfPattern_omitted P F A r hr v f hf) i else transferRowEmbedding labels i) : Fin r ↪ V) := by
      cases b <;> rfl
    rw [hgraph]
    intro z w hzw
    rw [SimpleGraph.map_adj] at hzw
    obtain ⟨a,c,hac,rfl,rfl⟩ := hzw
    rw [← heval a,← heval c]
    apply hf.2.2.2
    rw [transferRowFullPosition_val,transferRowFullPosition_val]
    apply transferConstructionGraph_row_cycle r i _ hr _ a c hac
    cases b <;> simp

def transferConfigurationOfPattern (H : V → U → Prop) (u u' : U)
    (hroot : H v u ∧ H v u') (hA : ∀ z∈A,H z u ∧ H z u') :
    OrdinaryTransferConfiguration hr P F H v u u' where
  labels := transferLabelsOfPattern P F A r hr v f hf
  omitted := transferLabelsOfPattern_omitted P F A r hr v f hf
  rim_edges := transferLabelsOfPattern_rim P F A r hr v f hf
  spokes := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl|⟨a,rfl⟩
    · exact hroot
    · rw [transferLabelsOfPattern_apply]
      exact hA _ (hf.2.1 _)
  independent := by
    intro x hx y hy
    have hmem : ∀ z∈insert v (Set.range (transferLabelsOfPattern P F A r hr v f hf)),
        ∃ i : Fin (r^2+1),Fin.cons (α:=fun _=>V) v f i=z := by
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl|⟨a,rfl⟩
      · exact ⟨0,Fin.cons_zero _ _⟩
      · exact ⟨transferFullPosition r hr a,rfl⟩
    obtain ⟨i,rfl⟩ := hmem x hx
    obtain ⟨j,rfl⟩ := hmem y hy
    exact hf.2.2.1 i j

end Oberwolfach
