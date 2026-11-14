module

public import Oberwolfach.OrdinaryNonrootIsolatorCounts
public import Oberwolfach.OrdinaryInducedIsolatorEmbedding
public import Oberwolfach.FiniteConfigurationLoss

@[expose] public section
/-! Adaptive removal of root vertices and hubs has an explicit, deterministic
isolator-count loss; all configurations use the original host sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

theorem ordinary_nonroot_isolator_count_transfer
    (P Q F:SimpleGraph V) (H:V→U→Prop) (k:ℕ) (θ α:ℝ)
    (T:Finset V) (W:Finset U) (hk:3≤k) (hn:0<Fintype.card V)
    (hu:Fintype.card U≤Fintype.card V):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    ∀(x y:A),x≠y→
    (Fintype.card (OrdinaryIsolatorConfiguration P Q F H k θ α x.val y.val):ℝ)-
      Fintype.card (OrdinaryIsolatorConfiguration (P.induce (A:Set V)) (Q.induce (A:Set V))
        (F.induce (A:Set V)) (fun (v:A) (u:B)=>H v.val u.val) k θ α x y)≤
        ((T.card:ℝ)+W.card)*(Fintype.card V:ℝ)^(k-2):=by
  intro A B x y hxy
  have hxy':x.val≠y.val:=by intro h;exact hxy (Subtype.ext h)
  have hx:x.val∉T:=(Finset.mem_sdiff.mp x.property).2
  have hy:y.val∉T:=(Finset.mem_sdiff.mp y.property).2
  let good:=fun C:OrdinaryIsolatorConfiguration P Q F H k θ α x.val y.val=>
    C.hub∈B ∧ C.vertices.val⊆A
  have hl:=finite_configuration_loss good (ordinaryInducedIsolator P Q F H A B k θ α x y)
    (ordinary_induced_isolator_injective P Q F H A B k θ α x y)
  have hf (C:OrdinaryIsolatorConfiguration P Q F H k θ α x.val y.val):
      (if good C then (0:ℝ) else 1)=
      if C.hub∈W ∨ ∃z∈T,z∈C.vertices.val then 1 else 0:=by
    have he:¬good C ↔ C.hub∈W ∨ ∃z∈T,z∈C.vertices.val:=by
      simp only [good,A,B,Finset.mem_sdiff,Finset.mem_univ,true_and,Finset.subset_iff]
      push_neg
      tauto
    by_cases hg:good C
    · have hn:¬(C.hub∈W ∨ ∃z∈T,z∈C.vertices.val):=fun hh=>(he.mpr hh) hg
      simp [hg,hn]
    · have hh:=he.mp hg
      simp [hg,hh]
  calc
    _ ≤ ∑ C:OrdinaryIsolatorConfiguration P Q F H k θ α x.val y.val,if good C then (0:ℝ) else 1:=by
      convert hl using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    _ = ∑ C:OrdinaryIsolatorConfiguration P Q F H k θ α x.val y.val,
        if C.hub∈W ∨ ∃z∈T,z∈C.vertices.val then (1:ℝ) else 0:=Finset.sum_congr rfl (fun C _=>hf C)
    _ ≤ _:=by
      convert ordinary_isolator_excluded_roots_loss hxy' hk hn hu T W hx hy using 1 <;>
        congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
