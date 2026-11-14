module

public import Oberwolfach.MarkedNeighbourhoodEmbeddingCounts

@[expose] public section

/-! The exact request maps transfer all bounded-order neighbourhood estimates
on fixed domains, without changing their absolute errors or density profiles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem markedRowsWithSpokes_embedding
    (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (P:SimpleGraph V) (d h:ℕ) (A:Finset W)
    (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (c:Γ) (j:Color) (err:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hr:MarkedRowsWithSpokes P π d h (A.image f) p k q s c j err σ H):
    MarkedRowsWithSpokes (P.comap f) ρ d h A p k (fun u=>q (g u)) (fun u=>s (g u)) c j err
      (rawMarkedRestrictPair f g σ) (fun b x u=>H b (f x) (g u)):=by
  intro S T J hS hT hJ hinj
  let e:=markedRowRequestEmbedding f.toEmbedding
  let kJ: (Bool×Z)↪(Bool×U):=(Function.Embedding.refl Bool).prodMap g
  have hJi:Set.InjOn (fun a:Bool×U=>a.2) (J.image kJ):=by
    intro a ha b hb he
    obtain ⟨a,hja,rfl⟩:=Finset.mem_image.mp ha
    obtain ⟨b,hjb,rfl⟩:=Finset.mem_image.mp hb
    exact congrArg kJ (hinj hja hjb (g.injective he))
  have hh:=hr (S.image e) (T.image e) (J.image kJ)
    (by simpa only [Finset.card_image_of_injective _ e.injective] using hS)
    (by simpa only [Finset.card_image_of_injective _ e.injective] using hT)
    (by simpa only [Finset.card_image_of_injective _ kJ.injective] using hJ) hJi
  dsimp only [e,kJ] at hh
  rw [markedRowDomain_image f π ρ hf,markedRowCountWithSpokes_embedding f g π ρ hf] at hh
  rw [Finset.card_image_of_injective _ f.injective,
    Finset.prod_image (fun _ _ _ _ he=>(markedRowRequestEmbedding f.toEmbedding).injective he),
    Finset.prod_image (fun _ _ _ _ he=>((Function.Embedding.refl Bool).prodMap g).injective he)] at hh
  exact hh

theorem markedIndicesWithSpokes_embedding
    (f:W↪oV) (g:Z↪U) (π:Equiv.Perm V) (ρ:Equiv.Perm W)
    (hf:∀ x,f (ρ x)=π (f x)) (d h:ℕ) (B:Finset Z)
    (q:U→Γ→ℝ) (s:U→Color→ℝ) (c:Γ) (j:Color) (err:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (hi:MarkedIndicesWithSpokes π d h (B.image g) q s c j err σ H):
    MarkedIndicesWithSpokes ρ d h B (fun u=>q (g u)) (fun u=>s (g u)) c j err
      (rawMarkedRestrictPair f g σ) (fun b x u=>H b (f x) (g u)):=by
  intro J hJ hsep
  let kJ:(Bool×W)↪(Bool×V):=(Function.Embedding.refl Bool).prodMap f.toEmbedding
  have hsep':∀ a∈J.image kJ,∀ b∈J.image kJ,a≠b→¬PermutationClose π (3*d) a.2 b.2:=by
    intro a ha b hb hne
    obtain ⟨a,hja,rfl⟩:=Finset.mem_image.mp ha
    obtain ⟨b,hjb,rfl⟩:=Finset.mem_image.mp hb
    exact fun hc=>hsep a hja b hjb (fun he=>hne (congrArg kJ he))
      ((permutationClose_embedding_iff f.toEmbedding ρ π hf (3*d) a.2 b.2).mp hc)
  have hh:=hi (J.image kJ) (by simpa only [Finset.card_image_of_injective _ kJ.injective] using hJ) hsep'
  dsimp only [kJ] at hh
  rw [markedIndexCountWithSpokes_embedding f.toEmbedding g,
    Finset.sum_image (fun _ _ _ _ he=>g.injective he)] at hh
  have hp (u:Z):(∏ a∈J.image ((Function.Embedding.refl Bool).prodMap f.toEmbedding),
      if a.1 then q (g u) c else s (g u) j)=
      ∏ a∈J,if a.1 then q (g u) c else s (g u) j:=by
    rw [Finset.prod_image (fun _ _ _ _ he=>((Function.Embedding.refl Bool).prodMap f.toEmbedding).injective he)]
    rfl
  simp only [hp] at hh
  exact hh

end Oberwolfach
