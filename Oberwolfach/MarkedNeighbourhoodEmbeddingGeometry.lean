module

public import Oberwolfach.MarkedNeighbourhoodSpokeChanges
public import Oberwolfach.RawMarkedPairRestriction
public import Oberwolfach.MarkedPermutationEmbedding

@[expose] public section

/-! Exact row-request and fixed-domain geometry under invariant embeddings.
The distinctness test is on the same physical edges on both domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W:Type} [Fintype V] [Fintype W] [LinearOrder V] [LinearOrder W]

def markedRowRequestEmbedding (f:W↪V):(Bool×Bool×W)↪(Bool×Bool×V):=
  (Function.Embedding.refl Bool).prodMap ((Function.Embedding.refl Bool).prodMap f)

theorem markedRowRim_embedding (f:W↪V) (a:Bool×Bool×W) (x:W):
    markedRowRim (markedRowRequestEmbedding f a) (f x)=
      Sum.map (Prod.map f f) (Prod.map f f) (markedRowRim a x):=by
  obtain ⟨b,c,y⟩:=a
  cases b <;> cases c <;> rfl

theorem markedRow_parent_embedding (f:W↪oV) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (a:Bool×Bool×W) (x:W):
    Sum.elim (fun xy=>P.Adj xy.1 xy.2) (fun xy=>P.Adj xy.1 (π xy.2))
      (markedRowRim (markedRowRequestEmbedding f.toEmbedding a) (f x))↔
    Sum.elim (fun xy=>(P.comap f).Adj xy.1 xy.2) (fun xy=>(P.comap f).Adj xy.1 (ρ xy.2))
      (markedRowRim a x):=by
  obtain ⟨b,c,y⟩:=a
  cases b <;> cases c <;>
    simp only [markedRowRim,markedRowRequestEmbedding,Function.Embedding.coe_prodMap,Prod.map_apply,
      Function.Embedding.refl_apply,Bool.false_eq_true,ite_false,ite_true,
      Sum.elim_inl,Sum.elim_inr,SimpleGraph.comap_adj,hf] <;> rfl

theorem markedRowEligible_embedding (f:W↪oV) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (b:ℕ) (a:Bool×Bool×W) (x:W):
    markedRowEligible P π b (markedRowRequestEmbedding f.toEmbedding a) (f x)↔
      markedRowEligible (P.comap f) ρ b a x:=by
  unfold markedRowEligible
  rw [markedRow_parent_embedding f π ρ hf P a x]
  exact and_congr (not_congr (permutationClose_embedding_iff f.toEmbedding ρ π hf b a.2.2 x)) Iff.rfl

theorem markedRowPhysical_embedding (f:W↪V) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (a:Bool×Bool×W) (x:W):
    markedPairPhysical π (markedRowRim (markedRowRequestEmbedding f a) (f x))=
      Sym2.map f (markedPairPhysical ρ (markedRowRim a x)):=by
  obtain ⟨b,c,y⟩:=a
  cases b <;> cases c <;>
    simp only [markedRowRim,markedRowRequestEmbedding,Function.Embedding.coe_prodMap,Prod.map_apply,
      Function.Embedding.refl_apply,Bool.false_eq_true,ite_false,ite_true,markedPairPhysical,
      Sum.elim_inl,Sum.elim_inr,Sym2.map_mk,hf]

theorem markedRow_physical_injective_embedding (f:W↪V) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (S:Finset (Bool×Bool×W)) (x:W):
    Set.InjOn (fun a=>markedPairPhysical π (markedRowRim a (f x)))
      (S.image (markedRowRequestEmbedding f))↔
    Set.InjOn (fun a=>markedPairPhysical ρ (markedRowRim a x)) S:=by
  constructor
  · intro h a ha b hb he
    apply (markedRowRequestEmbedding f).injective
    apply h (Finset.mem_image.mpr ⟨a,ha,rfl⟩) (Finset.mem_image.mpr ⟨b,hb,rfl⟩)
    change markedPairPhysical π (markedRowRim (markedRowRequestEmbedding f a) (f x))=
      markedPairPhysical π (markedRowRim (markedRowRequestEmbedding f b) (f x))
    rw [markedRowPhysical_embedding f π ρ hf,markedRowPhysical_embedding f π ρ hf]
    exact congrArg (Sym2.map f) he
  · intro h a ha b hb he
    obtain ⟨a,hsa,rfl⟩:=Finset.mem_image.mp ha
    obtain ⟨b,hsb,rfl⟩:=Finset.mem_image.mp hb
    change markedPairPhysical π (markedRowRim (markedRowRequestEmbedding f a) (f x))=
      markedPairPhysical π (markedRowRim (markedRowRequestEmbedding f b) (f x)) at he
    rw [markedRowPhysical_embedding f π ρ hf,markedRowPhysical_embedding f π ρ hf] at he
    exact congrArg (markedRowRequestEmbedding f) (h hsa hsb (Sym2.map.injective f.injective he))

theorem markedRowDomain_image (f:W↪oV) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (b:ℕ)
    (A:Finset W) (S T:Finset (Bool×Bool×W)):
    markedRowDomain P π b (A.image f) (S.image (markedRowRequestEmbedding f.toEmbedding))
      (T.image (markedRowRequestEmbedding f.toEmbedding))=
      (markedRowDomain (P.comap f) ρ b A S T).image f:=by
  unfold markedRowDomain
  rw [Finset.filter_image]
  apply congrArg (Finset.image f)
  apply Finset.filter_congr
  intro x hx
  simp only [Finset.forall_mem_image,markedRowEligible_embedding f π ρ hf,
    markedRow_parent_embedding f π ρ hf]
  exact and_congr Iff.rfl (and_congr (markedRow_physical_injective_embedding f.toEmbedding π ρ hf S x) Iff.rfl)

end Oberwolfach
