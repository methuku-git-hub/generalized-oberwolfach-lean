module

public import Oberwolfach.MarkedPaddingPairGeometry
public import Oberwolfach.MarkedPaddedArcSeparation

@[expose] public section

/-! Check every row hypothesis of the transformer on the two augmented
root graphs, including the four endpoints of each paired rim occurrence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S I:Type} [Fintype I] [DecidableEq V]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {m b:ℕ} {H₀ HK:V→U→Prop}

theorem marked_paired_padding_four_roots
    (C:Bool×I→MarkedWheel tail head ktail khead m π b H₀ HK)
    (v v':I→V) (p:Bool×I→(Fin m↪V)) (Z:Finset V)
    (hC:∀ j i k,(C (j,i)).1.val k=Fin.cons (α:=fun _=>V) (if j then v' i else v i) (p (j,i)) k)
    (hv:∀ i,v i∈Z∧v' i∈Z) (hpair:∀ i,¬PermutationClose π b (v i) (v' i))
    (hav:∀ i k,∀ z∈Z,¬PermutationClose π b (p i k) z)
    (hsep:∀ i j,∀ k k',p i k≠p j k'→¬PermutationClose π b (p i k) (p j k')):
    ∀ i k,∀ x∈({(C (false,i)).1.val k,(C (false,i)).1.val (finRotate (m+1) k),
      (C (true,i)).1.val k,(C (true,i)).1.val (finRotate (m+1) k)}:Finset V),
    ∀ y∈({(C (false,i)).1.val k,(C (false,i)).1.val (finRotate (m+1) k),
      (C (true,i)).1.val k,(C (true,i)).1.val (finRotate (m+1) k)}:Finset V),
    x≠y→¬PermutationClose π b x y:=by
  have hcs:∀ i:I,∀ j j':Bool,∀ k k':Fin (m+1),(C (j,i)).1.val k≠(C (j',i)).1.val k'→
      ¬PermutationClose π b ((C (j,i)).1.val k) ((C (j',i)).1.val k'):=by
    intro i j j' k k'
    simpa only [hC] using paired_padding_cycle_rows_separated p v v' Z hv hpair hav hsep i j j' k k'
  intro i k x hx y hy hxy
  have mem (x:V) (hx:x∈({(C (false,i)).1.val k,(C (false,i)).1.val (finRotate (m+1) k),
      (C (true,i)).1.val k,(C (true,i)).1.val (finRotate (m+1) k)}:Finset V)):
      ∃ (j:Bool) (q:Fin (m+1)),x=(C (j,i)).1.val q:=by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with hx|hx|hx|hx
    · exact ⟨false,k,hx⟩
    · exact ⟨false,finRotate (m+1) k,hx⟩
    · exact ⟨true,k,hx⟩
    · exact ⟨true,finRotate (m+1) k,hx⟩
  obtain ⟨j,q,rfl⟩:=mem x hx
  obtain ⟨j',q',rfl⟩:=mem y hy
  exact hcs i j j' q q' hxy

theorem marked_paired_padding_root_geometry
    (src dst:A→V) (row:S→V) (φ φ':V→V) (R R':Finset V) (hm:0<m)
    (C:Bool×I→MarkedWheel tail head ktail khead m π b H₀ HK)
    (v:I→V) (p:Bool×I→(Fin m↪V))
    (hC:∀ j i k,(C (j,i)).1.val k=Fin.cons (α:=fun _=>V) (if j then φ (v i) else v i) (p (j,i)) k)
    (hv:∀ i,v i∈R∧φ (v i)∈R')
    (hφ:∀ z∈R∪R',φ' z=φ z)
    (hmap:∀ i k,φ' ((C (false,i)).1.val k)=(C (true,i)).1.val k)
    (hroots:∀ e,src e∈R∧dst e∈R∧φ (src e)∈R'∧φ (dst e)∈R')
    (hsroots:∀ s,row s∈R∧φ (row s)∈R')
    (hvw:∀ e,¬PermutationClose π b (src e) (dst e))
    (hvw':∀ e,¬PermutationClose π b (φ (src e)) (φ (dst e)))
    (hfour:∀ e,∀ x∈({src e,dst e,φ (src e),φ (dst e)}:Finset V),
      ∀ y∈({src e,dst e,φ (src e),φ (dst e)}:Finset V),x≠y→¬PermutationClose π b x y)
    (hpair:∀ i,¬PermutationClose π b (v i) (φ (v i)))
    (hav:∀ i k,∀ z∈R∪R',¬PermutationClose π b (p i k) z)
    (hsep:∀ i j,∀ k k',p i k≠p j k'→¬PermutationClose π b (p i k) (p j k')):
    let sp:=paddingRimTail src (fun i=>(C (false,i)).1.val)
    let dp:=paddingRimHead dst (fun i=>(C (false,i)).1.val)
    let rp:=paddingSpokeRow row (fun i=>(C (false,i)).1.val)
    let R₁:=R∪pairedPaddingPrivateRows p false
    let R₂:=R'∪pairedPaddingPrivateRows p true
    (∀ e,sp e∈R₁∧dp e∈R₁∧φ' (sp e)∈R₂∧φ' (dp e)∈R₂)∧
    (∀ s,rp s∈R₁∧φ' (rp s)∈R₂)∧
    (∀ e,¬PermutationClose π b (sp e) (dp e))∧
    (∀ e,¬PermutationClose π b (φ' (sp e)) (φ' (dp e)))∧
    ∀ e,∀ x∈({sp e,dp e,φ' (sp e),φ' (dp e)}:Finset V),
      ∀ y∈({sp e,dp e,φ' (sp e),φ' (dp e)}:Finset V),x≠y→¬PermutationClose π b x y:=by
  have hφs:∀ e,φ' (src e)=φ (src e):=fun e=>hφ _ (Finset.mem_union_left _ (hroots e).1)
  have hφd:∀ e,φ' (dst e)=φ (dst e):=fun e=>hφ _ (Finset.mem_union_left _ (hroots e).2.1)
  have hφr:∀ s,φ' (row s)=φ (row s):=fun s=>hφ _ (Finset.mem_union_left _ (hsroots s).1)
  have hmem (j:Bool) (i:I) (k:Fin (m+1)):
      (C (j,i)).1.val k∈(if j then R' else R)∪pairedPaddingPrivateRows p j:=by
    rw [hC];exact paired_padding_cycle_row_mem p v (fun i=>φ (v i)) R R' hv j i k
  have hfourC:=marked_paired_padding_four_roots C v (fun i=>φ (v i)) p (R∪R') hC
    (fun i=>⟨Finset.mem_union_left _ (hv i).1,Finset.mem_union_right _ (hv i).2⟩) hpair hav hsep
  dsimp only
  refine ⟨?_,?_,?_,?_,?_⟩
  · rintro (a|⟨i,k⟩)
    · simp only [paddingRimTail,paddingRimHead,Sum.elim_inl,hφs,hφd]
      exact ⟨Finset.mem_union_left _ (hroots a).1,Finset.mem_union_left _ (hroots a).2.1,
        Finset.mem_union_left _ (hroots a).2.2.1,Finset.mem_union_left _ (hroots a).2.2.2⟩
    · simp only [paddingRimTail,paddingRimHead,Sum.elim_inr,hmap]
      exact ⟨hmem false i k,hmem false i _,hmem true i k,hmem true i _⟩
  · rintro (s|⟨i,k⟩)
    · simp only [paddingSpokeRow,Sum.elim_inl,hφr]
      exact ⟨Finset.mem_union_left _ (hsroots s).1,Finset.mem_union_left _ (hsroots s).2⟩
    · simp only [paddingSpokeRow,Sum.elim_inr,hmap]
      exact ⟨hmem false i k,hmem true i k⟩
  · exact padded_arcs_separated src dst hm (fun i=>(C (false,i)).1) hvw
  · rintro (a|⟨i,k⟩)
    · simpa only [paddingRimTail,paddingRimHead,Sum.elim_inl,hφs,hφd] using hvw' a
    · simpa only [paddingRimTail,paddingRimHead,Sum.elim_inr,hmap] using marked_cycle_adjacent_separated hm (C (true,i)).1 k
  · rintro (a|⟨i,k⟩)
    · simpa only [paddingRimTail,paddingRimHead,Sum.elim_inl,hφs,hφd] using hfour a
    · simpa only [paddingRimTail,paddingRimHead,Sum.elim_inr,hmap] using hfourC i k

end Oberwolfach
