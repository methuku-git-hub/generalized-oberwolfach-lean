module

public import Oberwolfach.MarkedMappedRealizationsRootPair
public import Oberwolfach.MarkedDiagramModels

@[expose] public section

/-! The four transformer inputs of the actual marked diagram. All edges
retain their original occurrence indices through the central collapse. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 36000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V U E K A S:Type} [Fintype V₀] [Fintype U₀]
    [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V₀] [DecidableEq U₀] [DecidableEq V] [DecidableEq U]
    [DecidableEq A] [DecidableEq S]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ}

theorem marked_four_diagram_inputs
    (G:IndexedMarkedGraph V₀ U₀ A S) (hG:G.IsBalanced (l+4))
    (L:IndexedMarkedHostRealization (indexedMarkedExpansion G (l+4) (by omega)) tail head ktail khead H₀ HK π b)
    (R:IndexedMarkedHostRealization (indexedMarkedExpansion (indexedMarkedComparison G (l+4) hG) (l+4) (by omega))
        tail head ktail khead H₀ HK π b)
    (T:∀ i:Fin 3,IndexedMarkedHostRealization (indexedMarkedExpansion (markedDiagramOldGraph G l hG i) (l+4) (by omega))
        tail head ktail khead H₀ HK π b)
    (hinj:∀ i,Function.Injective (T i).rows∧Function.Injective (T i).hubs)
    (hLd:∀ i,Disjoint (T i).rowSet L.rowSet∧Disjoint (T i).hubSet L.hubSet)
    (hRd:∀ i,Disjoint (T i).rowSet R.rowSet∧Disjoint (T i).hubSet R.hubSet)
    (hLs:∀ i,∀ v∈(T i).rowSet,∀ w∈L.rowSet,¬PermutationClose π b v w)
    (hRs:∀ i,∀ v∈(T i).rowSet,∀ w∈R.rowSet,¬PermutationClose π b v w)
    (hmid:∀ i j,i≠j→Disjoint (T i).rowSet (T j).rowSet∧Disjoint (T i).hubSet (T j).hubSet∧
      ∀ v∈(T i).rowSet,∀ w∈(T j).rowSet,¬PermutationClose π b v w)
    (B:Finset U) (hLB:L.hubSet⊆B) (hRB:R.hubSet⊆B) (hTB:∀ i,(T i).hubSet⊆B):
    ∃ P:Fin 4→MarkedRootPair tail head ktail khead H₀ HK π b (l+4)
        (A⊕((A⊕S)×Fin (l+5))) (S⊕((A⊕S)×Fin (l+5))),
      (∀ j,(P j).source=![(T 0).resources,(T 0).resources,(T 2).resources,(T 2).resources] j)∧
      (∀ j,(P j).image=![L.resources,(T 1).resources,(T 1).resources,R.resources] j)∧
      (∀ j,(P j).R=![(T 0).rowSet,(T 0).rowSet,(T 2).rowSet,(T 2).rowSet] j)∧
      (∀ j,(P j).R'=![L.rowSet,(T 1).rowSet,(T 1).rowSet,R.rowSet] j)∧
      ∀ j,(P j).B=B:=by
  let G₀:=indexedMarkedExpansion G (l+4) (by omega)
  let G₂:=indexedMarkedExpansion (indexedMarkedComparison G (l+4) hG) (l+4) (by omega)
  have hb₀:G₀.IsBalanced (l+4):=indexedMarkedExpansion_balanced G _ _ hG
  have hb₂:G₂.IsBalanced (l+4):=indexedMarkedExpansion_balanced _ _ _ (indexedMarkedComparison_balanced G _ hG)
  let T₀:IndexedMarkedHostRealization G₀ tail head ktail khead H₀ HK π b:=T 0
  let T₂:IndexedMarkedHostRealization G₂ tail head ktail khead H₀ HK π b:=T 2
  let T₁:IndexedMarkedHostRealization (indexedMarkedCentralExpansion G (l+4) (by omega)) tail head ktail khead H₀ HK π b:=T 1
  obtain ⟨P₀,h₀,h₀',hr₀,hr₀',hB₀⟩:=marked_mapped_realizations_root_pair G₀ G₀ hb₀ T₀ L id id rfl
    (hinj 0).1 (hinj 0).2 B (hTB 0) hLB (hLd 0).1 (hLd 0).2 (hLs 0)
  obtain ⟨P₁,h₁,h₁',hr₁,hr₁',hB₁⟩:=marked_mapped_realizations_root_pair G₀ _ hb₀ T₀ T₁
    (Sum.map (fun _=>()) id) (Sum.map (fun _=>()) id) (indexedMarkedExpansion_to_central G _ _)
    (hinj 0).1 (hinj 0).2 B (hTB 0) (hTB 1) (hmid 0 1 (by decide)).1
    (hmid 0 1 (by decide)).2.1 (hmid 0 1 (by decide)).2.2
  obtain ⟨P₂,h₂,h₂',hr₂,hr₂',hB₂⟩:=marked_mapped_realizations_root_pair G₂ _ hb₂ T₂ T₁
    (Sum.map (fun _=>()) id) (Sum.map (fun _=>()) id) (indexedMarkedComparisonExpansion_to_central G _ _ hG)
    (hinj 2).1 (hinj 2).2 B (hTB 2) (hTB 1) (hmid 2 1 (by decide)).1
    (hmid 2 1 (by decide)).2.1 (hmid 2 1 (by decide)).2.2
  obtain ⟨P₃,h₃,h₃',hr₃,hr₃',hB₃⟩:=marked_mapped_realizations_root_pair G₂ G₂ hb₂ T₂ R id id rfl
    (hinj 2).1 (hinj 2).2 B (hTB 2) hRB (hRd 2).1 (hRd 2).2 (hRs 2)
  refine ⟨![P₀,P₁,P₂,P₃],?_,?_,?_,?_,?_⟩
  all_goals intro j;fin_cases j <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals first
    | exact h₀
    | exact h₁
    | exact h₂
    | exact h₃
    | exact h₀'
    | exact h₁'
    | exact h₂'
    | exact h₃'
    | exact hr₀
    | exact hr₁
    | exact hr₂
    | exact hr₃
    | exact hr₀'
    | exact hr₁'
    | exact hr₂'
    | exact hr₃'
    | exact hB₀
    | exact hB₁
    | exact hB₂
    | exact hB₃


end Oberwolfach
