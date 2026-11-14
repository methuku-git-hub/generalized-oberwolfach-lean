module

public import Oberwolfach.RowCoverPackings

@[expose] public section

/-! Assemble row-root packings using a comparison deletion only on A.
The one-root existence premise is discharged by the bounded-deletion
construction in the subsequent application. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r n K:ℕ}

theorem sequential_ordinary_row_covers (x:Fin n→V) (hx:Function.Injective x)
    (A:Finset V) (hxA:∀ i,x i∉A)
    (hstep:∀ i:Fin n,∀ M:Finset (OrdinaryWheel Q F H r),
      (∀ W∈M,x i∉(ordinaryWheelRim W).support) →
      (∀ a∈A,(ordinaryWheelRimGraph M).degree a≤n*(2*(K+1))) →
      (∀ a∈A,(Finset.univ.filter (ordinaryPackingSpokes M a)).card≤n*(K+1)) →
      (∀ u,(Finset.univ.filter (fun a=>ordinaryPackingSpokes M a u)).card≤n*r) →
      ∃ N:Finset (OrdinaryWheel Q F H r),OrdinaryRowCover N (x i) A K ∧
        Disjoint (N.biUnion ordinaryWheelResources) (M.biUnion ordinaryWheelResources)) :
    ∃ C:Fin n→Finset (OrdinaryWheel Q F H r),
      (∀ i,OrdinaryRowCover (C i) (x i) A K) ∧
      (∀ i j,i≠j → Disjoint ((C i).biUnion ordinaryWheelResources) ((C j).biUnion ordinaryWheelResources)) := by
  let allowed:=fun (i:Fin n) (M:Finset (OrdinaryWheel Q F H r))=>OrdinaryRowCover M (x i) A K
  let compatible:=fun M N:Finset (OrdinaryWheel Q F H r)=>
    Disjoint (M.biUnion ordinaryWheelResources) (N.biUnion ordinaryWheelResources)
  obtain ⟨C,hC,hcross⟩:=sequential_select_prefix n allowed compatible ∅ (by
    intro i C hC
    let M:=Finset.univ.biUnion C
    have hMr (a:V) (ha:a∈A):(ordinaryWheelRimGraph M).degree a≤n*(2*(K+1)):=by
      have hd (j:Fin n):(ordinaryWheelRimGraph (C j)).degree a≤2*(K+1):=by
        by_cases hj:j.val < i.val
        · exact (hC.2.1 j hj).rimDegree a (fun he=>hxA j (he ▸ ha))
        · rw [hC.1 j (by omega),ordinaryWheelRimGraph_empty];simp
      have hh:=graph_iSup_local_degree_bound (fun j=>ordinaryWheelRimGraph (C j)) Finset.univ a (2*(K+1)) hd
      simp only [Finset.inter_univ,SimpleGraph.card_neighborFinset_eq_degree] at hh
      have hcard:(Finset.univ.filter (fun j:Fin n=>∃ b∈(Finset.univ:Finset V),(ordinaryWheelRimGraph (C j)).Adj a b)).card≤n:=by
        simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_le_card (Finset.filter_subset (fun j:Fin n=>∃ b∈(Finset.univ:Finset V),(ordinaryWheelRimGraph (C j)).Adj a b) Finset.univ)
      have hh':(⨆ j,ordinaryWheelRimGraph (C j)).degree a≤n*(2*(K+1)):=by
        exact hh.trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (2*(K+1)) hcard)
      convert hh' using 1
      rw [ordinaryWheelRimGraph_biUnion]
    have hMrow (a:V) (ha:a∈A):(Finset.univ.filter (ordinaryPackingSpokes M a)).card≤n*(K+1):=by
      have hj (j:Fin n):(Finset.univ.filter (ordinaryPackingSpokes (C j) a)).card≤K+1:=by
        by_cases hji:j.val < i.val
        · exact (hC.2.1 j hji).rowDegree a (fun he=>hxA j (he ▸ ha))
        · rw [hC.1 j (by omega)];simp [ordinaryPackingSpokes]
      have hh:=relation_iUnion_degree_bound (fun j=>ordinaryPackingSpokes (C j) a) (K+1) hj
      simpa only [Fintype.card_fin,←ordinaryPackingSpokes_biUnion,M] using hh
    have hMcol (u:U):(Finset.univ.filter (fun a=>ordinaryPackingSpokes M a u)).card≤n*r:=by
      have hj (j:Fin n):(Finset.univ.filter (fun a=>ordinaryPackingSpokes (C j) a u)).card≤r:=by
        by_cases hji:j.val < i.val
        · exact (hC.2.1 j hji).columnDegree u
        · rw [hC.1 j (by omega)];simp [ordinaryPackingSpokes]
      have hh:=relation_iUnion_degree_bound (fun j a=>ordinaryPackingSpokes (C j) a u) r hj
      simpa only [Fintype.card_fin,←ordinaryPackingSpokes_biUnion,M] using hh
    have hav:∀ W∈M,x i∉(ordinaryWheelRim W).support:=by
      intro W hW hix
      obtain ⟨j,_,hWj⟩:=Finset.mem_biUnion.mp hW
      have hji:j.val < i.val:=by
        by_contra hn
        rw [hC.1 j (by omega)] at hWj
        exact Finset.notMem_empty _ hWj
      rcases (hC.2.1 j hji).support W hWj (x i) hix with he|he
      · have hh:=congrArg Fin.val (hx he);omega
      · exact hxA i he
    obtain ⟨N,hN,hNM⟩:=hstep i M hav hMr hMrow hMcol
    refine ⟨N,hN,?_⟩
    intro j hj
    apply hNM.symm.mono_left
    intro e he
    obtain ⟨W,hW,heW⟩:=Finset.mem_biUnion.mp he
    exact Finset.mem_biUnion.mpr ⟨W,Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hW⟩,heW⟩)
  refine ⟨C,hC,?_⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with h|h
  · exact hcross i j h
  · exact (hcross j i h).symm

end Oberwolfach
