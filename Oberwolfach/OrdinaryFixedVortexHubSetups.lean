module

public import Oberwolfach.OrdinaryEligibleHost
public import Oberwolfach.OrdinaryHubSetupGeneralFromBalance
public import Oberwolfach.OrdinaryFixedVortexConflict
public import Oberwolfach.OrdinaryVortexLevelParentDensityBalance
public import Oberwolfach.MarkedFixedVortexParentDegrees
public import Oberwolfach.MarkedFixedVortexAmbientBounds

@[expose] public section
/-! Fixed fractional weights, the original vortex means and bounded
permutation conflicts give every local hub-weight setup before sampling. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_fixed_vortex_hub_setups
    (m d:ℕ) (P:SimpleGraph V) (D vsize:ℕ) (β ε θhost α ρ₀ pmin pR pH ξ cLo cHi b Bweight ηHub Kdom:ℝ)
    (Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (hreg:P.IsRegularOfDegree D) (hn:0<Fintype.card V) (hθ:1/2≤θhost) (hα:0<α)
    (hdegree:(θhost+α)*Fintype.card V≤D) (hρ₀:0<ρ₀)
    (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβα:β≤α/8) (hβ1:β≤1/4) (hε:0<ε) (hv:0<vsize)
    (hpmin:0<pmin) (hpmin1:pmin≤1) (hpR:pmin≤pR) (hpR1:pR≤1)
    (hpH:pmin≤pH) (hpH1:pH≤1) (hpEq:pR=initialIndexDensity U D*pH)
    (hcLo:0<cLo) (hcHi:0≤cHi) (hK:2/ε≤Kdom) (hb:b≤cLo)
    (hB:(4*cHi/pmin^(3*m+1))*Kdom^m≤Bweight)
    (weight:∀i,OrdinaryCycle ((P.comap (markedVortexVertexEmbedding Q i)).induce
      ((markedVortexInnerVertices Q i):Set (markedVortexVertexType Q i))) (m+1)→ℝ)
    (hweight:∀i,i<Q.length→
      (∀C,cLo/((markedVortexInnerVertices Q i).card:ℝ)^(m-1)≤weight i C ∧
        weight i C≤cHi/((markedVortexInnerVertices Q i).card:ℝ)^(m-1)) ∧
      (∀x y,(∑C,if C.val.val.Adj x y then weight i C else 0)=
        if ((P.comap (markedVortexVertexEmbedding Q i)).induce
          ((markedVortexInnerVertices Q i):Set (markedVortexVertexType Q i))).Adj x y then 1 else 0))
    (herr:∀i,i<Q.length→ξ+2*β+12*((m+1:ℕ):ℝ)^4*cHi*(2*((3*d:ℕ):ℝ))/
      (markedVortexInnerVertices Q i).card≤ηHub):
    ∀i,i<Q.length→
    let f:=markedVortexVertexEmbedding Q i;let I:=markedVortexInnerVertices Q i;
    let B:=markedVortexInnerHubs Q i;let F:=permutationConflictGraph π (3*d);
    OrdinaryInnerHubWeightSetupGeneral m (P.comap f) (F.comap f) I (weight i)
      pmin pR pH (2*pH*B.card/pR) β ξ (2*((3*d:ℕ):ℝ)) cLo cHi b Bweight ηHub Kdom:=by
  intro i hi f I B F
  have hρ:0< initialIndexDensity U D:=hρ₀.trans_le hρlo
  have hpRpos:0<pR:=hpmin.trans_le hpR
  have hpHpos:0<pH:=hpmin.trans_le hpH
  have hDhalf:(Fintype.card V:ℝ)/2≤D:=by
    have hh:=mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤θhost+α by linarith) (show (0:ℝ)≤Fintype.card V by positivity)
    nlinarith only [hh,hdegree]
  have hDmargin:(1/2+α)*Fintype.card V≤D:=by
    have hh:=mul_le_mul_of_nonneg_right (show (1/2+α:ℝ)≤θhost+α by linarith) (show (0:ℝ)≤Fintype.card V by positivity)
    exact hh.trans hdegree
  have hambient:=marked_vortex_fixed_ambient_size_fields Q hreg hn hDhalf hρ₀ hρlo hρhi hβ hβ1 hε hv i hi
  have hIpos:0<I.card:=by
    have hi':i+1≤Q.length:=by omega
    have hh:=Q.vertices_lower hi'
    have hreal:(0:ℝ)<ε*(vsize:ℝ)/2:=by positivity
    have hc:(0:ℝ)<(Q.vertices (i+1)).card:=hreal.trans_le hh
    have heq:I.card=(Q.vertices (i+1)).card:=by
      rw [(marked_vortex_inner_cardinalities Q i).1,Q.extendedVertices_eq hi']
    rw [heq]
    exact_mod_cast hc
  have hfields:=ordinary_vortex_level_parent_density_balance P D vsize β ε θhost α (initialIndexDensity U D) pH
    Q hn hreg rfl hρ hβ hpHpos.le hdegree i (by omega)
  have hparent:∀v,|pR*((P.comap f).neighborFinset v∩I).card-2*pH*B.card|≤pR*β*I.card:=by
    intro v
    have hh:=hfields.2 v
    rw [hpEq]
    simpa only [Finset.inter_comm] using hh
  have hcenter:((I.card:ℝ)/2≤2*(B.card:ℝ)/initialIndexDensity U D) ∧
      (2*(B.card:ℝ)/initialIndexDensity U D≤2*I.card):=by
    obtain ⟨x,hx⟩:=Finset.card_pos.mp hIpos
    have hx':x.val∈Q.vertices ((i+1)-2):=by
      have hh: x.val∈Q.extendedVertices ((i+1)-2):=Q.extendedVertices_subset (by omega) x.property
      rwa [Q.extendedVertices_eq (by omega:(i+1)-2≤Q.length)] at hh
    have hf:=Q.marked_parent_degrees hreg hn hDmargin hα hρ hβ hβα hβ1 (show i+1≤Q.length by omega) x.val hx'
    have hIeq:I.card=(Q.vertices (i+1)).card:=by
      rw [(marked_vortex_inner_cardinalities Q i).1,Q.extendedVertices_eq (by omega:i+1≤Q.length)]
    have hBeq:B.card=(Q.indices (i+1)).card:=by
      rw [(marked_vortex_inner_cardinalities Q i).2.2.1,Q.extendedIndices_eq (by omega:i+1≤Q.length)]
    simpa only [hIeq,hBeq] using ⟨hf.1,hf.2.1⟩
  have hcenterEq:2*pH*(B.card:ℝ)/pR=2*(B.card:ℝ)/initialIndexDensity U D:=by
    rw [hpEq]
    field_simp [hρ.ne',hpHpos.ne']
  have hlo:pR*(I.card:ℝ)/2≤2*pH*B.card:=by
    have hh:=mul_le_mul_of_nonneg_left hcenter.1 hpRpos.le
    have he: pR*(2*(B.card:ℝ)/initialIndexDensity U D)=2*pH*B.card:=by
      rw [hpEq];field_simp [hρ.ne']
    nlinarith only [hh,he]
  have hhi:2*pH*(B.card:ℝ)≤2*pR*I.card:=by
    have hh:=mul_le_mul_of_nonneg_left hcenter.2 hpRpos.le
    have he: pR*(2*(B.card:ℝ)/initialIndexDensity U D)=2*pH*B.card:=by
      rw [hpEq];field_simp [hρ.ne']
    nlinarith only [hh,he]
  have hregscale:(pR*β*(I.card:ℝ))/pR≤β*I.card:=by
    field_simp [hpRpos.ne']
    exact le_rfl
  have hconf:∀v,(((F.comap f).degree v):ℝ)≤2*((3*d:ℕ):ℝ):=by
    intro v
    have he:=ordinary_fixed_vortex_conflict_restriction P D vsize β ε Q π hπ i (3*d)
    let ρ:=markedVortexPermutation Q π hπ i
    have hh:=permutationConflictGraph_degree_le ρ (3*d) v
    have hcard:=congrArg (fun G:SimpleGraph (markedVortexVertexType Q i)=>G.neighborFinset v) he
    have hdegreeEq:=congrArg Finset.card hcard
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at hdegreeEq
    have hnat:((F.comap f).degree v)≤2*(3*d):=by
      convert hdegreeEq.le.trans hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    exact_mod_cast hnat
  have hK0:0≤Kdom:=le_trans (by positivity:0≤2/ε) hK
  have hsize:(Fintype.card (markedVortexVertexType Q i):ℝ)≤Kdom*I.card:=by
    have hh:=hambient.1
    have hA:(0:ℝ)≤I.card:=by positivity
    have hk:=mul_le_mul_of_nonneg_right hK hA
    have hh':(Fintype.card (markedVortexVertexType Q i):ℝ)≤(2/ε)*I.card:=by
      calc
        _ ≤ (2*(I.card:ℝ))/ε:=(le_div_iff₀ hε).mpr (by nlinarith only [hh])
        _ = (2/ε)*I.card:=by ring
    exact hh'.trans hk
  exact ordinary_hub_setup_general_from_balance m (P.comap f) (F.comap f) I B (weight i)
    pmin pR pH (pR*β*I.card) β ξ (2*((3*d:ℕ):ℝ)) cLo cHi b Bweight ηHub Kdom
    hIpos hpmin hpmin1 hpR hpR1 hpH hpH1 hβ (by positivity) hcLo hcHi hK0
    hparent hlo hhi hregscale hconf (hweight i hi).1 (hweight i hi).2 hsize hb hB (herr i hi)
end Oberwolfach
