module

public import Oberwolfach.MarkedHostReindexing
public import Oberwolfach.MarkedFiniteResourceSupport

@[expose] public section

/-! Reindex a packing between equivalent typed hosts and identify its
actual remainder. Divisibility is derived by subtracting the packing in
the destination host, not postulated for a resource set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K E' K':Type}
    [Fintype V] [Fintype U] [Fintype E] [Fintype K] [Fintype E'] [Fintype K']
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]
    [DecidableEq E'] [DecidableEq K']

theorem markedHostReindex_packing
    (tail head:E → V) (ktail khead:K → V) (tail' head':E' → V) (ktail' khead':K' → V)
    (H₀ HK:V → U → Prop) (π:Equiv.Perm V) (m b:ℕ) (e:E≃E') (k:K≃K')
    (ht:∀ a,tail' (e a)=tail a) (hh:∀ a,head' (e a)=head a)
    (hkt:∀ a,ktail' (k a)=ktail a) (hkh:∀ a,khead' (k a)=khead a)
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (hM:∀ Y∈M,∀ Z∈M,Y≠Z → Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Z)) :
    ∃ N:Finset (MarkedWheel tail' head' ktail' khead' m π b H₀ HK),
      (∀ Y∈N,∀ Z∈N,Y≠Z → Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Z)) ∧
      N.biUnion markedWheelPhysicalResources=M.biUnion markedWheelPhysicalResources := by
  let f:=Function.Embedding.refl V
  let g:=Function.Embedding.refl U
  let φ:MarkedWheel tail head ktail khead m π b H₀ HK ↪
      MarkedWheel tail' head' ktail' khead' m π b H₀ HK := markedWheelVertexEmbedding f g (fun _=>rfl) e k ht hh hkt hkh (fun _ _ h=>h) (fun _ _ h=>h)
  refine ⟨M.image φ,markedPackingVertexEmbedding_matching f g (fun _=>rfl) e k ht hh hkt hkh
    (fun _ _ h=>h) (fun _ _ h=>h) M hM,?_⟩
  have h:=markedPackingVertexEmbedding_resources f g (fun _=>rfl) e k ht hh hkt hkh
    (fun _ _ h=>h) (fun _ _ h=>h) M
  have hi:(markedResourceEmbedding f g : (Finset V⊕(V×U)) → (Finset V⊕(V×U)))=id:=
    funext markedResourceEmbedding_refl
  rw [hi,Finset.image_id] at h
  exact h

theorem markedHostReindex_packing_remainder
    (tail head:E → V) (ktail khead:K → V) (tail' head':E' → V) (ktail' khead':K' → V)
    (H₀ HK:V → U → Prop) (π:Equiv.Perm V) (m b:ℕ) (e:E≃E') (k:K≃K')
    (ht:∀ a,tail' (e a)=tail a) (hh:∀ a,head' (e a)=head a)
    (hkt:∀ a,ktail' (k a)=ktail a) (hkh:∀ a,khead' (k a)=khead a)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hp':Function.Injective (markedPhysicalEdge tail' head' ktail' khead' π))
    (hH:∀ v u,¬(H₀ v u∧HK v u)) :
    let S:=Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2);
    MarkedRemainderDivisible tail' head' ktail' khead' HK Finset.univ S m →
    ∀ M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK),
    (∀ Y∈M,∀ Z∈M,Y≠Z → Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Z)) →
    ∃ N:Finset (MarkedWheel tail' head' ktail' khead' m π b H₀ HK),
      (∀ Y∈N,∀ Z∈N,Y≠Z → Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Z)) ∧
      N.biUnion markedWheelPhysicalResources=M.biUnion markedWheelPhysicalResources ∧
      MarkedRemainderDivisible tail' head' ktail' khead' HK (Finset.univ\N.biUnion markedWheelArcs)
        (S\N.biUnion markedWheelSpokePairs) m ∧
      markedFiniteResources tail' head' ktail' khead' π (Finset.univ\N.biUnion markedWheelArcs) (S\N.biUnion markedWheelSpokePairs)=
        markedFiniteResources tail head ktail khead π (Finset.univ\M.biUnion markedWheelArcs) (S\M.biUnion markedWheelSpokePairs) := by
  intro S hd M hM
  obtain ⟨N,hN,hR⟩:=markedHostReindex_packing tail head ktail khead tail' head' ktail' khead' H₀ HK π m b e k ht hh hkt hkh M hM
  have hNA:N.biUnion markedWheelArcs⊆Finset.univ:=Finset.subset_univ _
  have hNS:N.biUnion markedWheelSpokePairs⊆S:=by
    intro s hs
    obtain ⟨W,_,hs⟩:=Finset.mem_biUnion.mp hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,markedWheelPhysicalResources_spoke_present W s.1 s.2 ((markedWheel_spoke_resource W s).mp hs)⟩
  refine ⟨N,hN,hR,marked_packing_remainder_divisible hH Finset.univ S hd N hN hNA hNS,?_⟩
  rw [markedFiniteResources_sdiff _ _ _ _ π hp',markedPackingResources_eq_finite,
    markedFiniteResources_sdiff _ _ _ _ π hp,markedPackingResources_eq_finite,hR]
  have hu:(Finset.univ:Finset (E⊕K)).image (e.toEmbedding.sumMap k.toEmbedding)=Finset.univ:=by
    apply Finset.image_univ_of_surjective
    intro a
    cases a with
    | inl a=>exact ⟨Sum.inl (e.symm a),by simp⟩
    | inr a=>exact ⟨Sum.inr (k.symm a),by simp⟩
  have heq:=markedHostReindex_resources tail head ktail khead tail' head' ktail' khead' π e k ht hh hkt hkh Finset.univ S
  rw [hu] at heq
  rw [heq]

end Oberwolfach
