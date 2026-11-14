module

public import Oberwolfach.OrdinaryActualCentralMaps
public import Oberwolfach.OrdinaryFiniteModelOrder
public import Oberwolfach.OrdinaryJointExpansionEmbeddings

@[expose] public section

/-! The three expansions in the ordinary absorber diagram, with their
actual edge/spoke identifiers. The middle expansion has one old row and
one old hub; the last is built from the decomposable comparison graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀:Type} [Fintype V₀] [Fintype U₀] [DecidableEq V₀] [DecidableEq U₀]

def ordinaryDiagramOldRows (G:SimpleGraph V₀) (r:ℕ) : Fin 3→Type :=
  ![V₀,Unit,OrdinaryComparisonRows r (G.edgeFinset.card/r)]
def ordinaryDiagramOldHubs (G:SimpleGraph V₀) (r:ℕ) : Fin 3→Type :=
  ![U₀,Unit,OrdinaryComparisonHubs (G.edgeFinset.card/r)]
def ordinaryDiagramEdges (G:SimpleGraph V₀) (r:ℕ) (hr:3≤r) : Fin 3→Type :=
  ![G.edgeFinset,G.edgeFinset,(ordinaryComparisonRim r (G.edgeFinset.card/r) (by omega)).edgeFinset]
def ordinaryDiagramSpokes (G:SimpleGraph V₀) (Hs:V₀→U₀→Prop) (r:ℕ) (hr:3≤r) : Fin 3→Type :=
  ![ActualSpoke Hs,ActualSpoke Hs,ActualSpoke (ordinaryComparisonSpokes r (G.edgeFinset.card/r) (by omega))]

instance ordinaryDiagramOldRows_fintype (G:SimpleGraph V₀) (r:ℕ) (i:Fin 3) : Fintype (ordinaryDiagramOldRows G r i) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i=>Fin.elim0 i))) i <;> dsimp [ordinaryDiagramOldRows] <;> infer_instance
instance ordinaryDiagramOldHubs_fintype (G:SimpleGraph V₀) (r:ℕ) (i:Fin 3) : Fintype (ordinaryDiagramOldHubs (U₀:=U₀) G r i) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i=>Fin.elim0 i))) i <;> dsimp [ordinaryDiagramOldHubs] <;> infer_instance
instance ordinaryDiagramEdges_fintype (G:SimpleGraph V₀) (r:ℕ) (hr:3≤r) (i:Fin 3) : Fintype (ordinaryDiagramEdges G r hr i) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i=>Fin.elim0 i))) i <;> dsimp [ordinaryDiagramEdges] <;> infer_instance
instance ordinaryDiagramSpokes_fintype (G:SimpleGraph V₀) (Hs:V₀→U₀→Prop) (r:ℕ) (hr:3≤r) (i:Fin 3) : Fintype (ordinaryDiagramSpokes G Hs r hr i) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i=>Fin.elim0 i))) i <;> dsimp [ordinaryDiagramSpokes] <;> infer_instance

def ordinaryDiagramX (G:SimpleGraph V₀) (r:ℕ) (hr:3≤r) :
    ∀ i:Fin 3,ordinaryDiagramEdges G r hr i→ ordinaryDiagramOldRows G r i := by
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i=>Fin.elim0 i))) i
  · exact fun e=>e.val.out.1
  · exact fun _=>()
  · exact fun e=>e.val.out.1

def ordinaryDiagramY (G:SimpleGraph V₀) (r:ℕ) (hr:3≤r) :
    ∀ i:Fin 3,ordinaryDiagramEdges G r hr i→ ordinaryDiagramOldRows G r i := by
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i=>Fin.elim0 i))) i
  · exact fun e=>e.val.out.2
  · exact fun _=>()
  · exact fun e=>e.val.out.2

def ordinaryDiagramV (G:SimpleGraph V₀) (Hs:V₀→U₀→Prop) (r:ℕ) (hr:3≤r) :
    ∀ i:Fin 3,ordinaryDiagramSpokes G Hs r hr i→ ordinaryDiagramOldRows G r i := by
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i=>Fin.elim0 i))) i
  · exact fun e=>e.val.1
  · exact fun _=>()
  · exact fun e=>e.val.1

def ordinaryDiagramU (G:SimpleGraph V₀) (Hs:V₀→U₀→Prop) (r:ℕ) (hr:3≤r) :
    ∀ i:Fin 3,ordinaryDiagramSpokes G Hs r hr i→ ordinaryDiagramOldHubs (U₀:=U₀) G r i := by
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i=>Fin.elim0 i))) i
  · exact fun e=>e.val.2
  · exact fun _=>()
  · exact fun e=>e.val.2

abbrev ordinaryDiagramExpansionRim (G:SimpleGraph V₀) (Hs:V₀→U₀→Prop) (r:ℕ) (hr:3≤r) (i:Fin 3) :=
  ordinaryExpansionRim (J:=ordinaryDiagramSpokes G Hs r hr i) (SimpleGraph.cycleGraph r)
    ⟨0,by omega⟩ ⟨r-1,by omega⟩ (ordinaryDiagramX G r hr i) (ordinaryDiagramY G r hr i)
abbrev ordinaryDiagramExpansionSpokes (G:SimpleGraph V₀) (Hs:V₀→U₀→Prop) (r:ℕ) (hr:3≤r) (i:Fin 3) :=
  ordinaryExpansionSpokes (E:=ordinaryDiagramEdges G r hr i) (⟨0,by omega⟩:Fin r)
    (ordinaryDiagramV G Hs r hr i) (ordinaryDiagramU G Hs r hr i)

/-- A single bound for both attachments and all three expansions. -/
def ordinaryDiagramSize (r m:ℕ) : ℕ :=
  2+m+2*m^2*(r+1)+m^2*(r+2)+2*(m^2*(r+2))^2*(r+1)

theorem ordinary_diagram_model_size (G:SimpleGraph V₀) (Hs:V₀→U₀→Prop) (r m:ℕ) (hr:3≤r)
    (hm:Fintype.card V₀+Fintype.card U₀≤m) :
    ∀ i:Fin 3,Fintype.card (ordinaryDiagramOldRows G r i)+Fintype.card (ordinaryDiagramOldHubs (U₀:=U₀) G r i)+
      (Fintype.card (ordinaryDiagramEdges G r hr i)+Fintype.card (ordinaryDiagramSpokes G Hs r hr i))*(r+1)≤ordinaryDiagramSize r m := by
  have he:G.edgeFinset.card≤m^2:=(simpleGraph_edges_le_square G).trans (Nat.pow_le_pow_left (by omega) 2)
  have hs:Fintype.card (ActualSpoke Hs)≤m^2:=by
    have hh:=Fintype.card_subtype_le (fun e:V₀×U₀=>Hs e.1 e.2)
    simp only [Fintype.card_prod] at hh
    exact hh.trans (by simpa only [pow_two] using Nat.mul_le_mul (show Fintype.card V₀≤m by omega) (show Fintype.card U₀≤m by omega))
  have hL:=actual_expansion_order_bound G Hs r m hm
  rw [ordinaryExpansion_order] at hL
  simp only [Fintype.card_fin] at hL
  have hJ:=ordinary_comparison_order_bound G r m (by omega)
  have hJexp:=actual_expansion_order_bound (ordinaryComparisonRim r (G.edgeFinset.card/r) (by omega))
    (ordinaryComparisonSpokes r (G.edgeFinset.card/r) (by omega)) r (m^2*(r+2)) hJ
  rw [ordinaryExpansion_order] at hJexp
  simp only [Fintype.card_fin] at hJexp
  have hLM:m+2*m^2*(r+1)≤ordinaryDiagramSize r m:=by dsimp [ordinaryDiagramSize];omega
  have hJM:m^2*(r+2)+2*(m^2*(r+2))^2*(r+1)≤ordinaryDiagramSize r m:=by dsimp [ordinaryDiagramSize];omega
  intro i
  fin_cases i
  · simpa [ordinaryDiagramOldRows,ordinaryDiagramOldHubs,ordinaryDiagramEdges,ordinaryDiagramSpokes,
      Matrix.cons_val_zero,Fintype.card_coe] using hL.trans hLM
  · dsimp [ordinaryDiagramOldRows,ordinaryDiagramOldHubs,ordinaryDiagramEdges,ordinaryDiagramSpokes]
    simp only [Fintype.card_unit,Fintype.card_coe]
    have hsum:G.edgeFinset.card+Fintype.card (ActualSpoke Hs)≤2*m^2:=by omega
    have hh:=Nat.mul_le_mul_right (r+1) hsum
    dsimp [ordinaryDiagramSize]
    omega
  · simpa [ordinaryDiagramOldRows,ordinaryDiagramOldHubs,ordinaryDiagramEdges,ordinaryDiagramSpokes,
      Matrix.cons_val_two,Matrix.cons_val_one,Matrix.cons_val_zero] using hJexp.trans hJM

end Oberwolfach
