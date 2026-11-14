module

public import Oberwolfach.OrdinaryNonrootCutUniformMargins
public import Oberwolfach.OrdinaryNonrootDeepUniformMargins
public import Oberwolfach.OrdinaryFixedVortexCleanupDomainGeometry
public import Oberwolfach.OrdinaryFixedVortexConflict

@[expose] public section
/-! Derive the numerical nonroot cut and deep-cover inputs simultaneously
at every fixed vortex level from the original regular-host geometry. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 36000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fixed_vortex_nonroot_uniform_margins
    (ρ₀ pmin href a ρ θ aLoad:ℝ) (hρ₀:0<ρ₀) (hpmin:0<pmin) (hhref:0<href)
    (ha:0<a) (hρ:0<ρ) (hθ:0<θ) (haLoad:0<aLoad):
    ∃δcut ζcut εcut ζlimit εsample εvortex:ℝ,
      0<δcut ∧ δcut<1/4 ∧ 0<ζcut ∧ 0<εcut ∧ 0<ζlimit ∧ 0<εsample ∧ 0<εvortex ∧ εvortex<1/4 ∧
    ∀ε:ℝ,0<ε→ε≤εvortex→∀β:ℝ,0≤β→β≤1/4→∀d:ℕ,∃v₀:ℕ,1≤v₀ ∧
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (i:ℕ),i<Q.length→
    ∀(pH εR εH Ledit:ℝ),pmin≤pH→0≤εR→εR≤εsample→0≤εH→εH≤εsample→0≤Ledit→
      Ledit≤ζlimit*(markedVortexInnerVertices Q i).card→
    let I:=markedVortexInnerVertices Q i;let T:=markedVortexDeeperVertices Q i;
    let B:=markedVortexInnerHubs Q i;let W:=markedVortexDeeperHubs Q i;
    let n:ℝ:=Fintype.card (markedVortexVertexType Q i);
    let F:SimpleGraph (markedVortexVertexType Q i):=(permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i);
    let Lbase:=ζlimit*I.card;let L:=ρ*n/2;
    T⊆I ∧ W⊆B ∧ 0<I.card ∧ 0<B.card ∧ (ρ₀/8)*(I.card:ℝ)≤B.card ∧ B.card≤I.card ∧
    (T.card:ℝ)≤ε*I.card ∧ (W.card:ℝ)≤ε*B.card ∧
    δcut≤pH/16 ∧ ζcut≤pH^2/128 ∧ 2*ε≤pH/8 ∧ 2*ε≤href-ζlimit ∧
    εH*B.card+2*Ledit≤εcut*B.card ∧ εH*B.card+Ledit≤pH*B.card/2 ∧
    εR*I.card+Ledit≤pH*I.card/2 ∧
    3*εcut*(I.card:ℝ)^2*(B.card:ℝ)^2+((2*(3*d)+1:ℕ):ℝ)*I.card*(B.card:ℝ)^2≤
      (ζcut*I.card*B.card)^2 ∧
    (I.card:ℝ)≤a*n ∧ (T.card:ℝ)≤θ*n ∧ 2*(W.card:ℝ)≤L ∧ 0≤L ∧ L≤ρ*n ∧
    (∀v,(F.degree v:ℝ)≤L) ∧ Ledit≤Lbase ∧ Lbase+I.card≤L ∧ Lbase+B.card≤L ∧ 4≤aLoad^2*n := by
  obtain ⟨h₀,δcut,ζcut,εcut,ζlimit,εsample,hh₀,hδ,hδsmall,hζ,hεcut,hζlimit,hεsample,hcut⟩:=
    ordinary_nonroot_cut_uniform_margins (ρ₀/8) pmin href (by positivity) hpmin hhref
  obtain ⟨εdeep,hεdeep,hεdeep1,hdeep⟩:=ordinary_nonroot_deep_uniform_margins a ρ θ aLoad ζlimit ha hρ hθ haLoad hζlimit
  let εvortex:ℝ:=min (1/8) (min h₀ εdeep)
  have hεv:0<εvortex:=lt_min (by norm_num) (lt_min hh₀ hεdeep)
  have hεv1:εvortex<1/4:=(min_le_left _ _).trans_lt (by norm_num)
  have hεvh:εvortex≤h₀:=(min_le_right _ _).trans (min_le_left _ _)
  have hεvd:εvortex≤εdeep:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δcut,ζcut,εcut,ζlimit,εsample,εvortex,hδ,hδsmall,hζ,hεcut,hζlimit,hεsample,hεv,hεv1,?_⟩
  intro ε hε hεvortex β hβ hβ1 d
  have hε1:ε<1/4:=hεvortex.trans_lt hεv1
  obtain ⟨Ncut,hNcut,hcut⟩:=hcut (2*(3*d))
  obtain ⟨Ndeep,hNdeep,hdeep⟩:=hdeep ε hε.le (hεvortex.trans hεvd) (2*(3*d))
  obtain ⟨v₀,hv₀,hgeom⟩:=ordinary_fixed_vortex_cleanup_domain_geometry β ε ρ₀ hβ hβ1 hε hε1 hρ₀ (max Ncut Ndeep)
  refine ⟨v₀,hv₀,?_⟩
  intro V U _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv Q π hπ i hi pH εR εH Ledit hpH hεR0 hεR hεH0 hεH hL0 hL I T B W n F Lbase L
  have hg:=hgeom V U P D vsize hreg hn hD hρlo hρhi hv Q i hi
  have hI0:(0:ℝ)≤I.card:=by positivity
  have hB0:(0:ℝ)≤B.card:=by positivity
  have hT0:(0:ℝ)≤T.card:=by positivity
  have hW0:(0:ℝ)≤W.card:=by positivity
  have hInat:max Ncut Ndeep≤I.card:=hg.2.2.1
  have hBnat:max Ncut Ndeep≤B.card:=hg.2.2.2.1
  have hIpositive:0<I.card:=lt_of_lt_of_le (by omega) hInat
  have hBpositive:0<B.card:=lt_of_lt_of_le (by omega) hBnat
  have hIratio:(I.card:ℝ)≤ε*n:=by
    have hh:=(Q.extended_successor_size_bounds hε.le i).1
    have hIeq:(I.card:ℝ)=(Q.extendedVertices (i+1)).card:=by exact_mod_cast (marked_vortex_inner_cardinalities Q i).1
    have hneq:n=(Q.extendedVertices i).card:=by simp [n,markedVortexVertexType]
    rw [←hIeq,←hneq] at hh
    exact hh
  have hNcutI:(Ncut:ℝ)≤I.card:=by
    exact_mod_cast (show Ncut≤I.card from (le_max_left _ _).trans hInat)
  have hNdeepn:(Ndeep:ℝ)≤n:=by
    have hh:Ndeep≤I.card:=(le_max_right _ _).trans hInat
    have hi':I.card≤Fintype.card (markedVortexVertexType Q i):=Finset.card_le_univ I
    change (Ndeep:ℝ)≤(Fintype.card (markedVortexVertexType Q i):ℝ)
    exact_mod_cast hh.trans hi'
  have htR0:0≤εR*(I.card:ℝ):=mul_nonneg hεR0 hI0
  have htH0:0≤εH*(B.card:ℝ):=mul_nonneg hεH0 hB0
  have htR:εR*(I.card:ℝ)≤εsample*I.card:=mul_le_mul_of_nonneg_right hεR hI0
  have htH:εH*(B.card:ℝ)≤εsample*B.card:=mul_le_mul_of_nonneg_right hεH hB0
  have hc:=hcut (I.card:ℝ) (B.card:ℝ) pH (εR*I.card) (εH*B.card) Ledit ε
    hNcutI hB0 hg.2.2.2.2.1 hpH htR0 htR htH0 htH hL0 hL hε.le (hεvortex.trans hεvh)
  have hd:=hdeep n I.card T.card B.card W.card Ledit hNdeepn hI0 hIratio hT0 hg.2.2.2.2.2.2.1
    hB0 (by exact_mod_cast hg.2.2.2.2.2.1) hW0 hg.2.2.2.2.2.2.2 hL0 hL
  have hF:∀v,(F.degree v:ℝ)≤L:=by
    intro v
    have heq: F=permutationConflictGraph (markedVortexPermutation Q π hπ i) (3*d):=
      ordinary_fixed_vortex_conflict_restriction P D vsize β ε Q π hπ i (3*d)
    have hfd:(F.degree v:ℝ)≤(2*(3*d):ℕ):=by
      have he:=congrArg (fun G:SimpleGraph (markedVortexVertexType Q i)=>G.neighborFinset v) heq
      have hcard:=congrArg Finset.card he
      simp only [SimpleGraph.card_neighborFinset_eq_degree] at hcard
      have hh:=permutationConflictGraph_degree_le (markedVortexPermutation Q π hπ i) (3*d) v
      have hf:F.degree v≤2*(3*d):=by
        convert hcard.le.trans hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
      exact_mod_cast hf
    exact hfd.trans hd.2.2.2.2.2.1
  refine ⟨hg.1,hg.2.1,hIpositive,hBpositive,hg.2.2.2.2.1,hg.2.2.2.2.2.1,
    hg.2.2.2.2.2.2.1,hg.2.2.2.2.2.2.2,hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,
    hc.2.2.2.2.1,hc.2.2.2.2.2.1,hc.2.2.2.2.2.2.1,?_,
    hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,hd.2.2.2.2.1,hF,hd.2.2.2.2.2.2.1,
    hd.2.2.2.2.2.2.2.1,hd.2.2.2.2.2.2.2.2.1,hd.2.2.2.2.2.2.2.2.2⟩
  convert hc.2.2.2.2.2.2.2 using 1 <;> push_cast <;> ring
end Oberwolfach
