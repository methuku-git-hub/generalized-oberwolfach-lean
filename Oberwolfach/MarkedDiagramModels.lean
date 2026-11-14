module

public import Oberwolfach.IndexedMarkedCentralExpansion

@[expose] public section

/-! The three finite expansions in the marked absorber diagram. Original
rim and spoke indices are retained through the central collapse. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ A S:Type} [Fintype V₀] [Fintype U₀] [Fintype A] [Fintype S]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq A] [DecidableEq S]

def markedDiagramOldRows (G:IndexedMarkedGraph V₀ U₀ A S) (l:ℕ):Fin 3→Type:=
  ![V₀,Unit,G.MarkedSpokes×Fin (l+5)]
def markedDiagramOldHubs (G:IndexedMarkedGraph V₀ U₀ A S):Fin 3→Type:=
  ![U₀,Unit,G.MarkedSpokes]

instance markedDiagramOldRows_fintype (G:IndexedMarkedGraph V₀ U₀ A S) (l:ℕ) (i:Fin 3):Fintype (markedDiagramOldRows G l i):=by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i=>Fin.elim0 i))) i <;> dsimp [markedDiagramOldRows] <;> infer_instance
instance markedDiagramOldHubs_fintype (G:IndexedMarkedGraph V₀ U₀ A S) (i:Fin 3):Fintype (markedDiagramOldHubs G i):=by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i=>Fin.elim0 i))) i <;> dsimp [markedDiagramOldHubs] <;> infer_instance

def markedDiagramOldGraph (G:IndexedMarkedGraph V₀ U₀ A S) (l:ℕ) (hG:G.IsBalanced (l+4)):
    ∀ i:Fin 3,IndexedMarkedGraph (markedDiagramOldRows G l i) (markedDiagramOldHubs G i) A S:=by
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i=>Fin.elim0 i))) i
  · exact G
  · exact G.map (fun _=>()) (fun _=>())
  · exact indexedMarkedComparison G (l+4) hG

def markedDiagramSize (l n e:ℕ):ℕ:=n+(2*e+1)*(l+6)+2

theorem marked_diagram_model_size (G:IndexedMarkedGraph V₀ U₀ A S) (l n e:ℕ)
    (hn:Fintype.card V₀+Fintype.card U₀≤n) (he:Fintype.card A+Fintype.card S≤e):
    (∀ i:Fin 3,Fintype.card (markedDiagramOldRows G l i)+Fintype.card (A⊕S)*(l+5)≤markedDiagramSize l n e)∧
    (∀ i:Fin 3,Fintype.card (markedDiagramOldHubs G i)+Fintype.card (A⊕S)≤markedDiagramSize l n e):=by
  have hm:Fintype.card G.MarkedSpokes≤Fintype.card S:=Fintype.card_subtype_le _
  have him:Fintype.card (A⊕S)≤e:=by simpa only [Fintype.card_sum] using he
  have hr:=Nat.mul_le_mul_right (l+5) him
  have hs:=Nat.mul_le_mul_right (l+5) (hm.trans (show Fintype.card S≤e by omega))
  constructor
  · intro i;fin_cases i <;> dsimp [markedDiagramOldRows,markedDiagramOldRows_fintype,Fin.cases,Fin.induction,Fin.induction.go] <;>
      (try simp only [Fintype.card_unit,Fintype.card_prod,Fintype.card_fin]) <;> dsimp [markedDiagramSize] <;> nlinarith
  · intro i;fin_cases i <;> dsimp [markedDiagramOldHubs,markedDiagramOldHubs_fintype,Fin.cases,Fin.induction,Fin.induction.go] <;>
      (try simp only [Fintype.card_unit]) <;> dsimp [markedDiagramSize] <;> nlinarith

end Oberwolfach
