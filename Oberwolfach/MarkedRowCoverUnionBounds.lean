module

public import Oberwolfach.MarkedRowCoverPackings

@[expose] public section

/-! Cumulative physical and spoke degrees of the completed row stage.
These are bounds on the actual union, including repeated hubs across rows. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head : E→V} {ktail khead : T→V} {H₀ HK : V→U→Prop}
    {π : Equiv.Perm V} {m b n K : ℕ}

theorem marked_row_cover_union_bounds
    (C : Fin n→Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (v : Fin n→V) (F : Finset V) (required : Fin n→Finset (Finset V⊕(V×U))) (Y : Fin n→Finset U)
    (hC : ∀ i,MarkedRowCover (C i) (v i) F (required i) (Y i) K) :
    let M := Finset.univ.biUnion C
    (∀ x,(spanningRestriction (markedPackingRimGraph M) F).degree x≤n*(4*(K+4))) ∧
    (∀ x∈F,(Finset.univ.filter (markedPackingSpokes M x)).card≤n*(K+4)) ∧
    (∀ u,(Finset.univ.filter (fun x=>markedPackingSpokes M x u)).card≤n*(m+1)) := by
  let M := Finset.univ.biUnion C
  refine ⟨?_,?_,?_⟩
  · intro x
    have he : spanningRestriction (markedPackingRimGraph M) F=
        ⨆ i,spanningRestriction (markedPackingRimGraph (C i)) F := by
      dsimp only [M]
      rw [markedPackingRimGraph_biUnion]
      ext z w
      simp only [spanningRestriction_adj,SimpleGraph.iSup_adj]
      aesop
    have hh := graph_iSup_local_degree_bound (fun i=>spanningRestriction (markedPackingRimGraph (C i)) F)
      Finset.univ x (4*(K+4)) (fun i=>(hC i).rimDegree x)
    simp only [Finset.inter_univ,SimpleGraph.card_neighborFinset_eq_degree] at hh
    have hi : (Finset.univ.filter (fun i:Fin n=>∃ z∈(Finset.univ:Finset V),
        (spanningRestriction (markedPackingRimGraph (C i)) F).Adj x z)).card≤n := by
      simpa using Finset.card_filter_le (s:=(Finset.univ:Finset (Fin n)))
        (p:=fun i=>∃ z∈(Finset.univ:Finset V),(spanningRestriction (markedPackingRimGraph (C i)) F).Adj x z)
    have hg := hh.trans (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (4*(K+4)) hi)
    convert hg using 1 <;> rw [he]
  · intro x hx
    have hh := relation_iUnion_degree_bound (fun i=>markedPackingSpokes (C i) x) (K+4)
      (fun i=>(hC i).rowDegree x hx)
    simpa only [Fintype.card_fin,←markedPackingSpokes_biUnion,M] using hh
  · intro u
    have hh := relation_iUnion_degree_bound (fun i x=>markedPackingSpokes (C i) x u) (m+1)
      (fun i=>(hC i).columnDegree u)
    simpa only [Fintype.card_fin,←markedPackingSpokes_biUnion,M] using hh

theorem marked_row_cover_unique_auxiliary_root
    (C : Fin n→Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (v : Fin n→V) (F : Finset V) (required : Fin n→Finset (Finset V⊕(V×U))) (Y : Fin n→Finset U)
    (hvF : ∀ i,v i∉F) (hC : ∀ i,MarkedRowCover (C i) (v i) F (required i) (Y i) K) :
    ∀ i W,W∈C i→markedWheelRows W∩Finset.univ.image v={v i} := by
  intro i W hW
  ext x
  constructor
  · intro hx
    obtain ⟨hxR,hxT⟩ := Finset.mem_inter.mp hx
    rcases Finset.mem_insert.mp ((hC i).rows W hW hxR) with he|he
    · exact Finset.mem_singleton.mpr he
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hxT
      exact False.elim (hvF j he)
  · intro hx
    rw [Finset.mem_singleton.mp hx]
    exact Finset.mem_inter.mpr ⟨(hC i).root W hW,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩

end Oberwolfach
