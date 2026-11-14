module

public import Oberwolfach.LongInnerTargetsAlignedWheelsLocal

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_aligned_source_occupancy_tests
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (m d:ℕ) (F:U→SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (P:SimpleGraph (Fin n)) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (Del:Finset (Sym2 (Fin n))) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t):
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let S:=longRawSurvivingResources P π d raw true true Del
    let hST:=long_raw_surviving_resources_subset P π d raw true true Del
    let q:=survivingCandidateEmbedding R S T hST
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S)))),
    ∀(assign:LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q)↪(Σw,(F w).ConnectedComponent)),
    (∀a,(assign a).1=(longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) a).val.2)→
    ∀(data:∀w,ActualResidualData
      (K:=(retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J w) ⊕
        {a:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true})
      (J:={a:LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) // (assign a).1=w}) (F w))
      (paths:∀w,retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J w→Fin ((m+1)*d+1)↪Fin n)
      (ψ:∀w,Fin n→Fin n),
    let occupied:=fun w=>((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (paths w)).image (ψ w)
    (∀w,(data w).s₂=secondSumIndices ∧
      (∀i∈(data w).s₂,∀j:Fin (d+1),∃x∈(data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (paths w),
        ψ w x=(π^j.val) (retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t J w i)) ∧
      (∀j:{a:LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) // (assign a).1=w},
        ∀v∈Finset.univ.image ((longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) j.val).val.1.val),v∈occupied w) ∧
      (∀W∈longRawMarkedWheelsAtHub P π d m ℓ raw true true (M.map q) w,∀i:Fin (m+1),W.1.val i∈occupied w))→
    (∀w x,rawIntervalFamilyState π d (fun e=>raw (Sum.inr e)) (x,w)=some (Sum.inl true)→x∈occupied w) ∧
    (∀(w:U) (a:LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q)),
      (longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) a).val.2=w→
      ∀v∈Finset.univ.image ((longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) a).val.1.val),v∈occupied w) ∧
    (∀w W,W∈longRawMarkedWheelsAtHub P π d m ℓ raw true true (M.map q) w→∀i:Fin (m+1),W.1.val i∈occupied w) :=by
  intro R T S hST q M assign hhub data paths ψ occupied hprops
  have happrox:∀w x,rawIntervalFamilyState π d (fun e=>raw (Sum.inr e)) (x,w)=some (Sum.inl true)→x∈occupied w:=by
    intro w
    apply long_approximate_labels_occupied_from_markers π d (fun e=>raw (Sum.inr e)) w (data w) (hprops w).1
      (bufferedPathStrictInterior (fun _=>(m+1)*d) (paths w)) (ψ w)
      (retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t J w)
    · intro b
      rfl
    · exact (hprops w).2.1
  have hOrd:∀(w:U) (a:LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q)),
      (longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) a).val.2=w→
      ∀v∈Finset.univ.image ((longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) a).val.1.val),v∈occupied w:=by
    intro w a ha
    exact (hprops w).2.2.1 ⟨a,(hhub a).trans ha⟩
  exact ⟨happrox,hOrd,fun w=>(hprops w).2.2.2⟩
end Oberwolfach
