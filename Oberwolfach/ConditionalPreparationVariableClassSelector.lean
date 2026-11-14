module

public import Oberwolfach.OrdinaryProtectedPreparationStatement
public import Oberwolfach.LongPreparationArbitraryCutoff
public import Oberwolfach.PreparationClassManuscriptHypotheses
public import Oberwolfach.ProtectedPreparationMonotone
public import Oberwolfach.ProtectedSets

@[expose] public section
/-! Conditional selector for all factor classes. Given the two manuscript
preparation propositions, one cutoff, perturbation tolerance and budget work
for every class; the sampling law and probability estimate stay unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem conditional_preparation_variable_class_selector
    (hOrd:OrdinaryProtectedPreparation) (hLong:LongProtectedPreparation)
    (θ α εlong ρstar:ℝ) (hθ:(1/2:ℝ)≤θ) (hθ1:θ<1)
    (hα:0<α) (hε:0<εlong) (hρstar:0<ρstar) (hρstar1:ρstar≤1)
    (KExtra:ℕ):
  ∃K₀:ℕ,KExtra≤K₀ ∧ 3≤K₀ ∧ ∀K:ℕ,K₀≤K→∀εshort:ℝ,0<εshort→∀ρshort:ℝ,0<ρshort→ρshort≤1→∃ξ:ℝ,0<ξ ∧ ∀χ:ℝ,0<χ→χ<1→∃B N:ℕ,1≤B ∧ 1≤N ∧
  ∀n≥N,∀(P:SimpleGraph (Fin n)) (D q:ℕ),
    P.IsRegularOfDegree D→Even D→(θ+α)*(n:ℝ)≤D→
  let ρ:ℝ:=2*(q:ℝ)/(D:ℝ);
  ∀(hρpos:0≤ρ) (hρhi:ρ≤1),
  ∀(Allowed:Set ℕ) (F:Fin q→SimpleGraph (Fin n)),
    allowedThreshold Allowed≤θ→(∀w,(F w).IsRegularOfDegree 2)→
    (∀w,AllowedCycleLengths (F w) Allowed)→
  ∀j:Option (Fin K),(∀w,factorPreparationClass (F w) K=j)→
  (j=none→ρstar≤ρ)→(∀i,j=some i→ρshort≤ρ)→
  ∃I:Finset (Fin n), (I.card:ℝ)≤(if j=none then εlong else εshort)*n ∧
    1-χ-1/(n:ℝ)^10≤
      (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin ρ
        hρpos hρhi)).probability
        (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) I ξ B F) :=by
  obtain ⟨K₀,hExtra,hK₀,ξL,hξL,hLongPrep⟩:=
    long_preparation_arbitrary_cutoff hLong θ α εlong ρstar hθ hθ1 hα hε hρstar hρstar1 KExtra
  refine ⟨K₀,hExtra,hK₀,?_⟩
  intro K hKK₀ εshort hεshort ρshort hρshort hρshort1
  have hK:3≤K:=hK₀.trans hKK₀
  let β:ℝ:=1/(2*(K:ℝ))
  have hβ:0<β:=by dsimp [β];positivity
  have hβ1:β≤1:=by
    dsimp [β]
    have hKr:(3:ℝ)≤K:=by exact_mod_cast hK
    rw [div_le_one (by positivity)]
    linarith
  have hEach:∀i:Fin K,∃ξ:ℝ,0<ξ ∧ ∀χ:ℝ,0<χ→χ<1→∃B N:ℕ,1≤B ∧ 1≤N ∧
      ∀n≥N,∀(P:SimpleGraph (Fin n)) (D q:ℕ),
      P.IsRegularOfDegree D→Even D→(θ+α)*(n:ℝ)≤D→
      let ρ:ℝ:=2*(q:ℝ)/(D:ℝ);
      ∀(hρlo:ρshort≤ρ) (hρhi:ρ≤1),∀F:Fin q→SimpleGraph (Fin n),
      (∀w,(F w).IsRegularOfDegree 2)→
      (∀w v,cycleThreshold (Fintype.card ((F w).connectedComponentMk v))≤θ)→
      (∀w,β*n≤((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=max 3 (i.val+1))).card:ℝ))→
      ∃I:Finset (Fin n),(I.card:ℝ)≤εshort*n ∧
      1-χ-1/(n:ℝ)^10≤(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin ρ (hρshort.le.trans hρlo) hρhi)).probability
        (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) I ξ B F):=by
    intro i
    exact hOrd θ α εshort ρshort β hθ hθ1 hα hεshort hρshort hρshort1 hβ hβ1 _ (le_max_left _ _)
  choose ξO hξO hOrdPrep using hEach
  obtain ⟨ξC,hξC,hξCle⟩:=positive_common_lower_bound (show 0<K by omega) ξO hξO
  let ξ:=min ξL ξC
  have hξ:0<ξ:=lt_min hξL hξC
  refine ⟨ξ,hξ,?_⟩
  intro χ hχ hχ1
  obtain ⟨BL,NL,hBL,hNL,hL⟩:=hLongPrep χ hχ hχ1
  have hEachχ:∀i:Fin K,∃B N:ℕ,1≤B ∧ 1≤N ∧
      ∀n≥N,∀(P:SimpleGraph (Fin n)) (D q:ℕ),
      P.IsRegularOfDegree D→Even D→(θ+α)*(n:ℝ)≤D→
      let ρ:ℝ:=2*(q:ℝ)/(D:ℝ);
      ∀(hρlo:ρshort≤ρ) (hρhi:ρ≤1),∀F:Fin q→SimpleGraph (Fin n),
      (∀w,(F w).IsRegularOfDegree 2)→
      (∀w v,cycleThreshold (Fintype.card ((F w).connectedComponentMk v))≤θ)→
      (∀w,β*n≤((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=max 3 (i.val+1))).card:ℝ))→
      ∃I:Finset (Fin n),(I.card:ℝ)≤εshort*n ∧
      1-χ-1/(n:ℝ)^10≤(FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.retentionCoin ρ (hρshort.le.trans hρlo) hρhi)).probability
        (fun σ=>ProtectedFactorPreparation P (retainedGraph P σ) I (ξO i) B F):=fun i=>hOrdPrep i χ hχ hχ1
  choose BO NO hBO hNO hO using hEachχ
  let B:=max BL (∑i:Fin K,BO i)
  let N:=max NL (∑i:Fin K,NO i)
  refine ⟨B,N,le_trans hBL (le_max_left _ _),le_trans hNL (le_max_left _ _),?_⟩
  intro n hn P D q hP hEven hdegree ρ hρpos hρhi Allowed F hAllowedThreshold hF hAllowed j hj hLongDensity hShortDensity
  have hn0:0<n:=by omega
  have hClass:∀w, (∀v,cycleThreshold (Fintype.card ((F w).connectedComponentMk v))≤allowedThreshold Allowed) ∧
      (factorPreparationClass (F w) K=none→(n:ℝ)/2≤((Finset.univ.filter (fun v=>K<Fintype.card ((F w).connectedComponentMk v))).card:ℝ)) ∧
      (∀i:Fin K,factorPreparationClass (F w) K=some i→3≤ i.val+1 ∧ β*n≤((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=i.val+1)).card:ℝ)):=by
    intro w
    exact preparation_class_manuscript_hypotheses hn0 hK (F w) (hF w) Allowed (hAllowed w)
  have hThreshold:∀w v,cycleThreshold (Fintype.card ((F w).connectedComponentMk v))≤θ:=
    fun w v=>((hClass w).1 v).trans hAllowedThreshold
  cases j with
  | none =>
    have hρlo:ρstar≤ρ:=hLongDensity rfl
    have hCounts:∀w,(n:ℝ)/2≤((Finset.univ.filter (fun v=>K<Fintype.card ((F w).connectedComponentMk v))).card:ℝ):=
      fun w=>(hClass w).2.1 (hj w)
    have hCounts₀:∀w,(n:ℝ)/2≤((Finset.univ.filter (fun v=>K₀<Fintype.card ((F w).connectedComponentMk v))).card:ℝ):=by
      intro w
      apply (hCounts w).trans
      have hsub:(Finset.univ.filter (fun v=>K<Fintype.card ((F w).connectedComponentMk v)))⊆
          (Finset.univ.filter (fun v=>K₀<Fintype.card ((F w).connectedComponentMk v))):=by
        intro v hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_of_le_of_lt hKK₀ (Finset.mem_filter.mp hv).2⟩
      exact_mod_cast Finset.card_le_card hsub
    obtain ⟨I,hI,hProb⟩:=hL n (by omega) P D q hP hEven hdegree hρlo hρhi F hF hThreshold hCounts₀
    refine ⟨I,by simpa using hI,hProb.trans ?_⟩
    exact protected_factor_preparation_probability_mono _ P (fun σ=>retainedGraph P σ) F I I ξL ξ BL B (by rfl) (min_le_left _ _) (le_max_left _ _)
  | some i =>
    have hρlo:ρshort≤ρ:=hShortDensity i rfl
    have hLen:3≤ i.val+1:=by
      by_cases hq:Nonempty (Fin q)
      · obtain ⟨w⟩:=hq
        exact ((hClass w).2.2 i (hj w)).1
      · have : q=0:=by simpa using hq
        subst q
        have hρzero:ρ=0:=by dsimp [ρ];simp
        linarith
    have hCounts:∀w,β*n≤((Finset.univ.filter (fun v=>Fintype.card ((F w).connectedComponentMk v)=max 3 (i.val+1))).card:ℝ):=by
      intro w
      rw [max_eq_right hLen]
      exact ((hClass w).2.2 i (hj w)).2
    have hNi:NO i≤n:=le_trans (Finset.single_le_sum (fun j _=>Nat.zero_le (NO j)) (Finset.mem_univ i)) (by omega)
    have hBi:BO i≤B:=le_trans (Finset.single_le_sum (fun j _=>Nat.zero_le (BO j)) (Finset.mem_univ i)) (le_max_right _ _)
    obtain ⟨I,hI,hProb⟩:=hO i n hNi P D q hP hEven hdegree hρlo hρhi F hF hThreshold hCounts
    refine ⟨I,by simpa using hI,hProb.trans ?_⟩
    exact protected_factor_preparation_probability_mono _ P (fun σ=>retainedGraph P σ) F I I (ξO i) ξ (BO i) B (by rfl) ((min_le_right _ _).trans (hξCle i)) hBi
end Oberwolfach
