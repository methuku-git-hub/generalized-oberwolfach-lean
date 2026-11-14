module

public import Oberwolfach.OrdinaryFixedColumnEmbedding

@[expose] public section
/-! One reservoir and one sample work for every target admitted by the
uniform postmatching-input theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 45000000
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem ordinary_uniform_column_embedding_eventually
    (m d:ℕ) (hm:7 ≤ m) (hd:2 ≤ d) (θ δ:ℝ) (hθ:0<θ) (hδ:0<δ):
    ∃N:ℕ,∀{n K:ℕ},N ≤ n → 0<n → 0<K → 
    ∀(U:Type) [Fintype U] [DecidableEq U],Fintype.card U ≤ n → 
    ∀(F₀:U → SimpleGraph (Fin n)) (hF₀:∀u,(F₀ u).IsRegularOfDegree 2)
    (Allowed:Set ℕ), (∀u,AllowedCycleLengths (F₀ u) Allowed) → 
    ∀(i₀:Fin K) (rsv:ℝ),0  ≤  rsv → rsv ≤ 1/100 → θ ≤ 1/100 → 
    OrdinaryClassReserveBound F₀ hF₀ i₀ rsv → 
    ∀(Cres:∀u,Finset (F₀ u).ConnectedComponent),
      (∀u (c:↥(Cres u)),Fintype.card c.val=i₀.val+1) → 
      (∀u,((i₀.val+1:ℕ):ℝ)*(Cres u).card=rsv*n) → 
    ∀(π:Equiv.Perm (Fin n)),(∀x l,0<l → l<2*d+1 → (π^l) x ≠ x) → 
    ∀(P:SimpleGraph (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (Inner:Finset (Fin n)) (Hubs:Finset U) (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×U)))
    (lamMatch a γ ζret κ b z ρ₀ smin lamList p:ℝ),
    0 ≤ ζret → 0 ≤ lamMatch+γ*(1-θ+lamMatch) → lamMatch+γ*(1-θ+lamMatch) ≤ θ/8 → 
    max a γ ≤ κ → 
    1/(8*(d:ℝ))+((m:ℝ)+1)*(d:ℝ)*ζret+(lamMatch+γ*(1-θ+lamMatch)) ≤ (δ/8)/2 → 
    2*θ+δ/8+((m:ℝ)+2)*κ ≤ δ → 
    0<ρ₀ → 0<smin → 0 ≤ b → 
    let αCap:=5*ρ₀*smin^2/128;
    16/(d:ℝ)+16*κ+16*b/αCap+4*z ≤ θ/8 → 
    ρ₀*n ≤ 4*(Fintype.card U:ℝ) → 
    (Hubs.card:ℝ) ≤ αCap*n → (n:ℝ)^(3/4:ℝ) ≤ αCap*n → b ≤ αCap/16 → b ≤ δ/8 → 
    4/(d:ℝ) ≤ δ/16 → 4*(n:ℝ)^(3/4:ℝ) ≤ δ*n/16 → 2*((max a γ)*n) ≤ δ*n/8 → 
    0<lamList → lamList/2 ≤ 1 → δ ≤ ((lamList/2)/100)^2 → 
    100/(lamList/2) ≤ (n:ℝ) → 2/Real.sqrt δ ≤ (n:ℝ) → 
    (∀u,(∑g:Bool,ordinaryAssignedMarkedProbability F₀ hF₀ K θ ((m:ℝ)+1) u g) ≤ 1/8) → 
    (∀u g,|rawIntervalHubStartCount π d g (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σ (Sum.inr e))) u-
      (n:ℝ)*ordinaryAssignedMarkedProbability F₀ hF₀ K θ ((m:ℝ)+1) u g/d|<(n:ℝ)^(3/4:ℝ)/d) → 
    OrdinaryZeroRetentionEvent π d false σ → OrdinaryBoundaryStartEvent π d σ → 
    ∀s:U → Bool → ℝ,OrdinaryReservedCompletionTests P π d p smin s σ → 
    ∀(Admissible:SimpleGraph (Fin n) → Prop),
      (∀S,Admissible S → OrdinaryFixedPostmatchingColumnInputs F₀ hF₀ Cres i₀ rsv θ lamMatch a γ m d π P S σ Inner Hubs Kabs lamList b z δ) → 
    ∀S,Admissible S → 
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4}
    let Conf:=permutationConflictGraph π (3*d)
    let Ref:=longPhysicalStateGraph P σ {0}\Conf
    let Protect:=ordinaryMatchingProtect Ref Inner Kabs
    let Del:=Sample\S
    let J:=ordinaryEmptyRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false);
    OrdinarySelectedPostmatchingEmbeddingTrackedResult F₀ hF₀ Cres i₀ rsv θ lamMatch a γ m d π P Del S Protect Sample Ref Conf σ 0 J
      Inner Hubs (ordinaryReservoirSpokeLabels Kabs) δ :=by
  have hfixed:=ordinary_fixed_column_embedding_eventually m d hm hd θ δ hθ hδ
  unfold OrdinaryFixedColumnEmbeddingShape at hfixed
  obtain ⟨N,hN⟩:=hfixed
  refine ⟨N,?_⟩
  intro n K hnN hn hK U _ _ hUn F₀ hF₀ Allowed hAllowed i₀ rsv hrs0 hrs1 hθ1 hClass Cres hsize hres π hnoshort
    P σ Inner Hubs Kabs lamMatch a γ ζret κ b z ρ₀ smin lamList p hζret hmatch0 hmatchUpper hκ hrate hsizeBudget
    hρ hs hb αCap hcapacity hUlo hHubs herror hbα hbδ hD hNsmall hRowRate hlamList hlamList1 hδbound
    hnβ hnδ hq hcounts hzero hboundary s htests Admissible hinputs S hS
  exact hN hnN hn hK U hUn F₀ hF₀ Allowed hAllowed i₀ rsv hrs0 hrs1 hθ1 hClass Cres hsize hres π hnoshort
    P S σ Inner Hubs Kabs lamMatch a γ ζret κ b z ρ₀ smin lamList p hζret hmatch0 hmatchUpper hκ hrate hsizeBudget
    hρ hs hb hcapacity hUlo hHubs herror hbα hbδ hD hNsmall hRowRate hlamList hlamList1 hδbound
    hnβ hnδ hq hcounts hzero hboundary s htests (hinputs S hS)
end Oberwolfach
