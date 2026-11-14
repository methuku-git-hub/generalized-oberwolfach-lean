module

public import Oberwolfach.LongRawRealizedFrequency
public import Oberwolfach.LongSelectedWheelComponentAssignment

@[expose] public section
/-! Selected ordinary raw candidates with the manuscript's frequency
estimate are assigned injectively to actual prescribed components. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawOrdinaryComponentFinDecidable (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_ordinary_candidates_assign_components (hn:0<n) (hK:0<K)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (ℓ:Fin K→ℕ)
    (θ lam:ℝ) (hlamθ:lam≤θ):
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let hub:=fun c:RestrictedResource (mixedCandidateResources R) e=>longRawSeedHub π d m ℓ c.val.1 c.val.2
    let idx:=fun c:RestrictedResource (mixedCandidateResources R) e=>c.val.1.getD ⟨0,hK⟩
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    (∀u i,
      let t:=longAssignedKeptFraction F hF K θ i u*(n:ℝ)/((i.val+1:ℕ):ℝ)
      |(((M.filter (fun c=>c.val.1=some i ∧ hub c=u)).card:ℝ)-(1-θ)*t)|≤lam*t) →
    ∃h:{c // c∈M.filter (fun c=>c.val.1.isSome)}↪(Σu,(F u).ConnectedComponent),
      ∀c,(h c).1=hub c.val ∧ Fintype.card (h c).2=(idx c.val).val+1 :=by
  intro state e R hub idx M herr
  let A:=M.filter (fun c=>c.val.1.isSome)
  let key:=fun c=>(hub c,idx c)
  have hfilter:∀u i,A.filter (fun c=>key c=(u,i))=
      M.filter (fun c=>c.val.1=some i ∧ hub c=u):=by
    intro u i
    ext c
    simp only [A,Finset.mem_filter]
    constructor
    · rintro ⟨⟨hc,hs⟩,hk⟩
      have hidx:idx c=i := (Prod.mk.inj hk).2
      have hsome:c.val.1=some (idx c):=by
        cases h:c.val.1 with
        | none => simp only [h,Option.isSome_none,Bool.false_eq_true] at hs
        | some j => simp only [idx,h,Option.getD_some]
      exact ⟨hc,hsome.trans (congrArg some hidx),(Prod.mk.inj hk).1⟩
    · rintro ⟨hc,hi,hu⟩
      refine ⟨⟨hc,?_⟩,?_⟩
      · simp only [hi,Option.isSome_some]
      · apply Prod.ext
        · exact hu
        · simp only [key,idx,hi,Option.getD_some]
  have he:∀u i,
      let t:=longAssignedKeptFraction F hF K θ i u*(n:ℝ)/((i.val+1:ℕ):ℝ)
      |(((A.filter (fun c=>key c=(u,i))).card:ℝ)-(1-θ)*t)|≤lam*t:=by
    intro u i
    rw [hfilter]
    exact herr u i
  apply long_selected_wheels_assign_components hn F hF A key θ lam hlamθ
  intro u i
  convert he u i using 1 <;>
    simp only [Finset.filter_congr_decidable]
end Oberwolfach
