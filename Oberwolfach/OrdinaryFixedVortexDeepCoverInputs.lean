module

public import Oberwolfach.OrdinaryDeepCoverLevelInputs
public import Oberwolfach.OrdinaryFixedVortexConflict
public import Oberwolfach.MarkedFixedVortexParentDegrees
public import Oberwolfach.MarkedFixedVortexAmbientBounds

@[expose] public section
/-! Derive the deep-cover host inputs at every fixed vortex level from the
original regular host, probability means and permutation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_fixed_vortex_deep_cover_inputs
    (m d:ℕ) (P:SimpleGraph V) (D vsize:ℕ) (β ε θhost α αdeep ρ₀ p ω a ε₀ pR pH:ℝ)
    (Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hθ:1/2≤θhost) (hthreshold:cycleThreshold (m+1)≤θhost)
    (hα:0<α) (hαdeep:αdeep≤α/2) (hdegree:(θhost+α)*Fintype.card V≤D)
    (hρ₀:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβα:β≤α/8) (hβ1:β≤1/4) (hβε:β≤ε₀)
    (hε:0<ε) (hεa:ε≤a) (hω:ω+ε≤ρ₀/8) (hvsize:0<vsize)
    (hnoshort:∀x k,0<k→k<2*d+1→(π^k) x≠x)
    (hpR:p≤pR) (hpR1:pR≤1) (hpH:p≤pH) (hpH1:pH≤1)
    (hpEq:pR=initialIndexDensity U D*pH):
    ∀i,i<Q.length→
      OrdinaryDeepCoverLevelInputs m (2*(3*d)) d αdeep p ω a ε₀
        (P.comap (markedVortexVertexEmbedding Q i))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
        (markedVortexPermutation Q π hπ i) (markedVortexInnerHubs Q i) pR pH
        (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity U D) β:=by
  intro i hi
  let W:=markedVortexVertexType Q i
  let Z:=markedVortexHubType Q i
  let f:W↪V:=(markedVortexVertexEmbedding Q i).toEmbedding
  let g:Z↪U:=markedVortexHubEmbedding Q i
  let ρ:=markedVortexPermutation Q π hπ i
  let J:=markedVortexInnerHubs Q i
  let Dlevel:ℝ:=2*(Fintype.card Z:ℝ)/initialIndexDensity U D
  have hρ:0< initialIndexDensity U D:=hρ₀.trans_le hρlo
  have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hDhalf:(Fintype.card V:ℝ)/2≤D:=by
    have hcoef:=mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤θhost+α by linarith) hnR.le
    nlinarith only [hcoef,hdegree]
  have hDmargin:(1/2+α)*Fintype.card V≤D:=by
    have hh:=mul_le_mul_of_nonneg_right (show (1/2+α:ℝ)≤θhost+α by linarith) hnR.le
    exact hh.trans hdegree
  have hfields:=marked_vortex_fixed_parent_degree_fields Q hreg hn hDmargin hα hρ hβ hβα hβ1 hε hvsize i hi
  have hambient:=marked_vortex_fixed_ambient_size_fields Q hreg hn hDhalf hρ₀ hρlo hρhi hβ hβ1 hε hvsize i hi
  have hW:Fintype.card W=(Q.vertices i).card:=by
    change Fintype.card (Q.extendedVertices i)=(Q.vertices i).card
    rw [Fintype.card_coe,Q.extendedVertices_eq hi.le]
  have hZ:Fintype.card Z=(Q.indices i).card:=by
    change Fintype.card (Q.extendedIndices i)=(Q.indices i).card
    rw [Fintype.card_coe,Q.extendedIndices_eq hi.le]
  have hcenter:|Dlevel-(D:ℝ)/Fintype.card V*(Fintype.card W:ℝ)|≤β*Fintype.card W:=by
    have hh:=(Q.estimates_including_zero hreg hn hρ hβ i hi.le).1
    simpa only [Dlevel,hW,hZ] using hh
  have hsize:((J.card:ℝ))≤ε*Fintype.card W:=by
    have hh:=(Q.extended_successor_size_bounds hε.le i).2
    have hJ:(J.card:ℝ)=(Q.extendedIndices (i+1)).card:=by exact_mod_cast (marked_vortex_inner_cardinalities Q i).2.2.1
    have hZi:(Fintype.card Z:ℝ)=(Q.extendedIndices i).card:=by simp [Z,markedVortexHubType]
    rw [←hJ,←hZi] at hh
    have hzw:(Fintype.card Z:ℝ)≤Fintype.card W:=by exact_mod_cast hambient.2.2
    exact hh.trans (mul_le_mul_of_nonneg_left hzw hε.le)
  have hJsmall:(J.card:ℝ)≤a*Fintype.card W:=hsize.trans
    (mul_le_mul_of_nonneg_right hεa (by positivity))
  have hUlower:(ρ₀/8)*(Fintype.card W:ℝ)≤Fintype.card Z:=by
    have hh:=Q.index_size_lower hreg hn hDhalf hρ₀ hρlo hβ hβ1 hi.le
    simpa only [hW,hZ] using hh
  have hcompl:((Finset.univ\J).card:ℝ)+(J.card:ℝ)=Fintype.card Z:=by
    have hc:(Finset.univ\J).card+J.card=Fintype.card Z:=by
      simpa only [Finset.card_univ] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ J)
    exact_mod_cast hc
  have hJlower:ω*Fintype.card W≤((Finset.univ\J).card:ℝ):=by
    have hh:=mul_le_mul_of_nonneg_right hω (show (0:ℝ)≤Fintype.card W by positivity)
    nlinarith only [hh,hUlower,hsize,hcompl]
  have hconf:(permutationConflictGraph π (3*d)).comap f=permutationConflictGraph ρ (3*d):=
    ordinary_fixed_vortex_conflict_restriction P D vsize β ε Q π hπ i (3*d)
  have hcomm:∀x,f (ρ x)=π (f x):=(marked_vortex_permutation_compatibility Q π hπ i).1
  have hshort:∀x k,0<k→k<2*d+1→(ρ^k) x≠x:=by
    intro x k hk hk' heq
    have hh:=congrArg f heq
    rw [permutation_embedding_power f π ρ hcomm k x] at hh
    exact hnoshort (f x) k hk hk' hh
  have hcoef:θhost+α≤(D:ℝ)/Fintype.card V:=(le_div_iff₀ hnR).mpr (by simpa [mul_comm] using hdegree)
  have hmin:∀x:W,(cycleThreshold (m+1)+αdeep)*Fintype.card W≤
      ((P.comap f).degree x:ℝ):=by
    intro x
    have hstart:=mul_le_mul_of_nonneg_right hcoef (show (0:ℝ)≤Fintype.card W by positivity)
    have hb:=mul_le_mul_of_nonneg_right hβα (show (0:ℝ)≤Fintype.card W by positivity)
    have ht:=mul_le_mul_of_nonneg_right (show cycleThreshold (m+1)+αdeep≤θhost+α-2*β by linarith)
      (show (0:ℝ)≤Fintype.card W by positivity)
    have hc1:=(abs_le.mp hcenter).1
    have hc2:-(β*(Fintype.card W:ℝ))≤((P.comap f).degree x:ℝ)-Dlevel:=by
      convert (abs_le.mp (hfields.2.1 x)).1 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    nlinarith only [hstart,hb,ht,hc1,hc2]
  have hbalance:pR*Dlevel=2*(Fintype.card Z:ℝ)*pH:=by
    rw [hpEq]
    dsimp [Dlevel]
    field_simp [hρ.ne']
    <;> ring
  refine ⟨hJsmall,hJlower,hambient.2.2,hmin,?_,?_,hshort,hpR,hpR1,hpH,hpH1,hfields.2.2.1,hβ,hβε,?_,hbalance⟩
  · intro x
    change ((permutationConflictGraph π (3*d)).comap f).degree x≤2*(3*d)
    have he:=congrArg (fun G:SimpleGraph W=>G.neighborFinset x) hconf
    have hc:=congrArg Finset.card he
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at hc
    have hh:=permutationConflictGraph_degree_le ρ (3*d) x
    convert hc.le.trans hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · change permutationConflictGraph ρ (3*d)≤(permutationConflictGraph π (3*d)).comap f
    rw [hconf]
  · exact hfields.2.1
end Oberwolfach
