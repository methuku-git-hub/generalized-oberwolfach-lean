module

public import Oberwolfach.RawNeighbourTestsExtendingList
public import Oberwolfach.MarkedSampleOccurrenceMatrix

@[expose] public section
/-! Distinct-endpoint two-path lower bounds imply all the neighbourhood tests
needed by the protected extending list, including the whole vertex set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_approx_two_paths_imply_neighbour_test_density
    {V:Type} [Fintype V] [LinearOrder V]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (ω:Sym2 V→Fin 6×Bool) (α:ℝ)
    (hV:2≤Fintype.card V)
    (hpaths:∀x y,x≠y→α*Fintype.card V≤
      ((Finset.univ.filter (fun v=>0<markedPhysicalRim P π (3*d)
        (fun e=>markedExpandedApproximateCollapse (ω e)) false x v ∧
        0<markedPhysicalRim P π (3*d)
        (fun e=>markedExpandedApproximateCollapse (ω e)) false v y)).card:ℝ)):
    ∀i,RawNeighbourTestValid i→α*Fintype.card V≤(rawApproxNeighbourTestSet P π d ω i).card:=by
  let D:=rawApproxPhysicalRelation P π d ω
  have hpos (x y:V):0<markedPhysicalRim P π (3*d)
      (fun e=>markedExpandedApproximateCollapse (ω e)) false x y ↔ D x y:=by
    dsimp [D,rawApproxPhysicalRelation]
    have h:=markedPhysicalRim_indicator P π (3*d) (fun e=>markedExpandedApproximateCollapse (ω e)) false x y
    split_ifs at h <;> omega
  have hcommon (x y:V) (hxy:x≠y):α*Fintype.card V≤
      ((directedOutNeighbours D x∩directedInNeighbours D y).card:ℝ):=by
    have heq:(Finset.univ.filter (fun v=>0<markedPhysicalRim P π (3*d)
        (fun e=>markedExpandedApproximateCollapse (ω e)) false x v ∧
        0<markedPhysicalRim P π (3*d)
        (fun e=>markedExpandedApproximateCollapse (ω e)) false v y))=
        directedOutNeighbours D x∩directedInNeighbours D y:=by
      ext v
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_inter,
        directedOutNeighbours,directedInNeighbours,hpos]
    simpa only [heq] using hpaths x y hxy
  haveI:Nontrivial V:=Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hsome (x:V):∃y:V,x≠y:=by
    obtain ⟨y,hy⟩:=exists_ne x
    exact ⟨y,Ne.symm hy⟩
  intro i hi
  rcases i with _|i
  · obtain ⟨x⟩:Nonempty V:=inferInstance
    obtain ⟨y,hxy⟩:=hsome x
    have hc:=hcommon x y hxy
    have hle:((directedOutNeighbours D x∩directedInNeighbours D y).card:ℝ)≤Fintype.card V:=by
      exact_mod_cast Finset.card_le_univ _
    simpa [rawApproxNeighbourTestSet] using hc.trans hle
  · rcases i with x|i
    · obtain ⟨y,hxy⟩:=hsome x
      have hc:=hcommon x y hxy
      have hle:((directedOutNeighbours D x∩directedInNeighbours D y).card:ℝ)≤(directedOutNeighbours D x).card:=by
        exact_mod_cast Finset.card_le_card Finset.inter_subset_left
      simpa [rawApproxNeighbourTestSet,D] using hc.trans hle
    · rcases i with y|xy
      · obtain ⟨x,hyx⟩:=hsome y
        have hc:=hcommon x y (Ne.symm hyx)
        have hle:((directedOutNeighbours D x∩directedInNeighbours D y).card:ℝ)≤(directedInNeighbours D y).card:=by
          exact_mod_cast Finset.card_le_card Finset.inter_subset_right
        simpa [rawApproxNeighbourTestSet,D] using hc.trans hle
      · rcases xy with ⟨x,y⟩
        exact hcommon x y hi
end Oberwolfach
