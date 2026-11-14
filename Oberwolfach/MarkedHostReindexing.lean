module

public import Oberwolfach.MarkedFiniteResourcesEmbedding
public import Oberwolfach.MarkedFiniteDomainBalanceEmbedding
public import Oberwolfach.MarkedDecompositionHostTransfer

@[expose] public section

/-! Reindex typed occurrences without changing vertices, hubs, or physical
resources. The balance comparisons hold at every original root and on the
same supplied domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K E' K':Type}
    [Fintype V] [Fintype U] [Fintype E] [Fintype K] [Fintype E'] [Fintype K']
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]
    [DecidableEq E'] [DecidableEq K']

theorem markedResourceEmbedding_refl (z:Finset V⊕(V×U)) :
    markedResourceEmbedding (Function.Embedding.refl V) (Function.Embedding.refl U) z=z := by
  cases z <;> simp [markedResourceEmbedding,Function.Embedding.sumMap,Function.Embedding.coe_refl,Prod.map_def]

theorem markedHostReindex_resources
    (tail head:E → V) (ktail khead:K → V) (tail' head':E' → V) (ktail' khead':K' → V)
    (π:Equiv.Perm V) (e:E≃E') (k:K≃K')
    (ht:∀ a,tail' (e a)=tail a) (hh:∀ a,head' (e a)=head a)
    (hkt:∀ a,ktail' (k a)=ktail a) (hkh:∀ a,khead' (k a)=khead a)
    (A:Finset (E⊕K)) (S:Finset (V×U)) :
    markedFiniteResources tail' head' ktail' khead' π (A.image (e.toEmbedding.sumMap k.toEmbedding)) S=
      markedFiniteResources tail head ktail khead π A S := by
  have h:=markedFiniteResources_embedding tail head ktail khead tail' head' ktail' khead'
    (Function.Embedding.refl V) (Function.Embedding.refl U) π π (fun _=>rfl)
    e.toEmbedding k.toEmbedding ht hh hkt hkh A S
  have hi : (markedResourceEmbedding (Function.Embedding.refl V) (Function.Embedding.refl U) : (Finset V⊕(V×U)) → (Finset V⊕(V×U))) = id := funext markedResourceEmbedding_refl
  rw [hi,Finset.image_id] at h
  simpa [Prod.map_def,Function.Embedding.coe_refl] using h.symm

theorem markedHostReindex_balance
    (tail head:E → V) (ktail khead:K → V) (tail' head':E' → V) (ktail' khead':K' → V)
    (HK HK':V → U → Prop) (e:E≃E') (k:K≃K')
    (ht:∀ a,tail' (e a)=tail a) (hh:∀ a,head' (e a)=head a)
    (hkt:∀ a,ktail' (k a)=ktail a) (hkh:∀ a,khead' (k a)=khead a)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ)
    (hHK:∀ z∈S,HK' z.1 z.2↔HK z.1 z.2) (z:V⊕U) (i:Fin 4) :
    markedFiniteBalance tail' head' ktail' khead' HK' (A.image (e.toEmbedding.sumMap k.toEmbedding)) S m z i=
      markedFiniteBalance tail head ktail khead HK A S m z i := by
  have h:=markedFiniteBalance_embedding tail head ktail khead tail' head' ktail' khead' HK HK'
    (Function.Embedding.refl V) (Function.Embedding.refl U) e.toEmbedding k.toEmbedding
    ht hh hkt hkh A S m hHK z i
  simpa [Prod.map_def,Function.Embedding.coe_refl] using h

theorem markedHostReindex_domain_balance
    (tail head:E → V) (ktail khead:K → V) (tail' head':E' → V) (ktail' khead':K' → V)
    (HK HK':V → U → Prop) (e:E≃E') (k:K≃K')
    (ht:∀ a,tail' (e a)=tail a) (hh:∀ a,head' (e a)=head a)
    (hkt:∀ a,ktail' (k a)=ktail a) (hkh:∀ a,khead' (k a)=khead a)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ)
    (hHK:∀ z∈S,HK' z.1 z.2↔HK z.1 z.2) (X:Finset V) (Z:Finset U) (z:V⊕U) (i:Fin 4) :
    markedFiniteDomainBalance tail' head' ktail' khead' HK' (A.image (e.toEmbedding.sumMap k.toEmbedding)) S m X Z z i=
      markedFiniteDomainBalance tail head ktail khead HK A S m X Z z i := by
  have h:=markedFiniteDomainBalance_embedding tail head ktail khead tail' head' ktail' khead' HK HK'
    (Function.Embedding.refl V) (Function.Embedding.refl U) e.toEmbedding k.toEmbedding
    ht hh hkt hkh A S m hHK X Z X Z (fun _=>Iff.rfl) (fun _=>Iff.rfl) z i
  simpa [Prod.map_def,Function.Embedding.coe_refl] using h

theorem markedHostReindex_divisible_iff
    (tail head:E → V) (ktail khead:K → V) (tail' head':E' → V) (ktail' khead':K' → V)
    (HK HK':V → U → Prop) (e:E≃E') (k:K≃K')
    (ht:∀ a,tail' (e a)=tail a) (hh:∀ a,head' (e a)=head a)
    (hkt:∀ a,ktail' (k a)=ktail a) (hkh:∀ a,khead' (k a)=khead a)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (m:ℕ)
    (hHK:∀ z∈S,HK' z.1 z.2↔HK z.1 z.2) :
    MarkedRemainderDivisible tail' head' ktail' khead' HK' (A.image (e.toEmbedding.sumMap k.toEmbedding)) S m ↔
      MarkedRemainderDivisible tail head ktail khead HK A S m := by
  rw [←markedFiniteBalance_eq_zero_iff,←markedFiniteBalance_eq_zero_iff]
  simp only [markedHostReindex_balance tail head ktail khead tail' head' ktail' khead' HK HK'
    e k ht hh hkt hkh A S m hHK]

theorem markedHostReindex_decomposition_iff
    (tail head:E → V) (ktail khead:K → V) (tail' head':E' → V) (ktail' khead':K' → V)
    (H₀ HK:V → U → Prop) (π:Equiv.Perm V) (m b:ℕ) (e:E≃E') (k:K≃K')
    (ht:∀ a,tail' (e a)=tail a) (hh:∀ a,head' (e a)=head a)
    (hkt:∀ a,ktail' (k a)=ktail a) (hkh:∀ a,khead' (k a)=khead a)
    (R:Finset (Finset V⊕(V×U))) :
    HasResourceDecomposition (fun W:MarkedWheel tail' head' ktail' khead' m π b H₀ HK=>markedWheelPhysicalResources W) R ↔
      HasResourceDecomposition (fun W:MarkedWheel tail head ktail khead m π b H₀ HK=>markedWheelPhysicalResources W) R := by
  constructor
  · intro h
    exact marked_decomposition_transfer_on_resources R
      (fun a _=>⟨e.symm a,by simpa using (ht (e.symm a)).symm,by simpa using (hh (e.symm a)).symm⟩)
      (fun a _=>⟨k.symm a,by simpa using (hkt (k.symm a)).symm,by simpa using (hkh (k.symm a)).symm⟩)
      (fun _ _ _ h=>h) (fun _ _ _ h=>h) h
  · intro h
    exact marked_decomposition_transfer_on_resources R
      (fun a _=>⟨e a,ht a,hh a⟩) (fun a _=>⟨k a,hkt a,hkh a⟩)
      (fun _ _ _ h=>h) (fun _ _ _ h=>h) h

end Oberwolfach
