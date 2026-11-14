module

public import Oberwolfach.MarkedRowCoverPackings

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
  {E T:Type} {tail head:E→V} {ktail khead:T→V} {H₀ HK:V→U→Prop}
  {π:Equiv.Perm V} {m b n K:ℕ}

theorem sequential_marked_row_covers (x:Fin n→V) (hx:Function.Injective x)
    (A:Finset V) (hxA:∀ i,x i∉A) (required:Fin n→Finset (Finset V⊕(V×U))) (allowedHubs:Fin n→Finset U)
    (hstep:∀ i:Fin n,∀ M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK),
      (∀ W∈M,x i∉markedWheelRows W) →
      (∀ a,(spanningRestriction (markedPackingRimGraph M) A).degree a≤n*(4*(K+4))) →
      (∀ a∈A,(Finset.univ.filter (markedPackingSpokes M a)).card≤n*(K+4)) →
      (∀ u,(Finset.univ.filter (fun a=>markedPackingSpokes M a u)).card≤n*(m+1)) →
      ∃ N:Finset (MarkedWheel tail head ktail khead m π b H₀ HK),MarkedRowCover N (x i) A (required i) (allowedHubs i) K ∧
        Disjoint (N.biUnion markedWheelPhysicalResources) (M.biUnion markedWheelPhysicalResources)) :
    ∃ C:Fin n→Finset (MarkedWheel tail head ktail khead m π b H₀ HK),
      (∀ i,MarkedRowCover (C i) (x i) A (required i) (allowedHubs i) K) ∧
      (∀ i j,i≠j → Disjoint ((C i).biUnion markedWheelPhysicalResources) ((C j).biUnion markedWheelPhysicalResources)) := by
  let allowed:=fun (i:Fin n) (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))=>MarkedRowCover M (x i) A (required i) (allowedHubs i) K
  let compatible:=fun M N:Finset (MarkedWheel tail head ktail khead m π b H₀ HK)=>
    Disjoint (M.biUnion markedWheelPhysicalResources) (N.biUnion markedWheelPhysicalResources)
  obtain ⟨C,hC,hcross⟩:=sequential_select_prefix n allowed compatible ∅ (by
    intro i C hC
    let M:=Finset.univ.biUnion C
    have hMr (a:V):(spanningRestriction (markedPackingRimGraph M) A).degree a≤n*(4*(K+4)):=by
      have hd (j:Fin n):(spanningRestriction (markedPackingRimGraph (C j)) A).degree a≤4*(K+4):=by
        by_cases hj:j.val < i.val
        · exact (hC.2.1 j hj).rimDegree a
        · rw [hC.1 j (by omega),markedPackingRimGraph_empty,spanningRestriction_degree]
          simp
      have he:spanningRestriction (markedPackingRimGraph M) A=
          ⨆ j,spanningRestriction (markedPackingRimGraph (C j)) A:=by
        dsimp only [M]
        rw [markedPackingRimGraph_biUnion]
        ext v w
        simp only [spanningRestriction_adj,SimpleGraph.iSup_adj]
        aesop
      have hh:=graph_iSup_local_degree_bound (fun j=>spanningRestriction (markedPackingRimGraph (C j)) A)
        Finset.univ a (4*(K+4)) hd
      simp only [Finset.inter_univ,SimpleGraph.card_neighborFinset_eq_degree] at hh
      have hcard:(Finset.univ.filter (fun j:Fin n=>∃ z∈(Finset.univ:Finset V),
          (spanningRestriction (markedPackingRimGraph (C j)) A).Adj a z)).card≤n:=by
        simpa using Finset.card_filter_le (s:=(Finset.univ:Finset (Fin n)))
          (p:=fun j=>∃ z∈(Finset.univ:Finset V),(spanningRestriction (markedPackingRimGraph (C j)) A).Adj a z)
      have hh':(⨆ j,spanningRestriction (markedPackingRimGraph (C j)) A).degree a≤n*(4*(K+4)):=
        hh.trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (4*(K+4)) hcard)
      convert hh' using 1 <;> rw [he]
    have hMrow (a:V) (ha:a∈A):(Finset.univ.filter (markedPackingSpokes M a)).card≤n*(K+4):=by
      have hj (j:Fin n):(Finset.univ.filter (markedPackingSpokes (C j) a)).card≤K+4:=by
        by_cases hji:j.val < i.val
        · exact (hC.2.1 j hji).rowDegree a ha
        · rw [hC.1 j (by omega)];simp [markedPackingSpokes]
      have hh:=relation_iUnion_degree_bound (fun j=>markedPackingSpokes (C j) a) (K+4) hj
      simpa only [Fintype.card_fin,←markedPackingSpokes_biUnion,M] using hh
    have hMcol (u:U):(Finset.univ.filter (fun a=>markedPackingSpokes M a u)).card≤n*(m+1):=by
      have hj (j:Fin n):(Finset.univ.filter (fun a=>markedPackingSpokes (C j) a u)).card≤m+1:=by
        by_cases hji:j.val < i.val
        · exact (hC.2.1 j hji).columnDegree u
        · rw [hC.1 j (by omega)];simp [markedPackingSpokes]
      have hh:=relation_iUnion_degree_bound (fun j a=>markedPackingSpokes (C j) a u) (m+1) hj
      simpa only [Fintype.card_fin,←markedPackingSpokes_biUnion,M] using hh
    have hav:∀ W∈M,x i∉markedWheelRows W:=by
      intro W hW hix
      obtain ⟨j,_,hWj⟩:=Finset.mem_biUnion.mp hW
      have hji:j.val < i.val:=by
        by_contra hn
        rw [hC.1 j (by omega)] at hWj
        exact Finset.notMem_empty _ hWj
      rcases Finset.mem_insert.mp ((hC.2.1 j hji).rows W hWj hix) with he|he
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
