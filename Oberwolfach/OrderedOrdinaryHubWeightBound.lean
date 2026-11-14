module

public import Oberwolfach.OrderedOrdinaryLoadBound
public import Oberwolfach.ResourceFullPatternConcentration

@[expose] public section
/-! A fixed hub carries at most linear total candidate weight, and its
weight at any single resource is bounded by the global root load. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {m b:ℕ} {π:Equiv.Perm V}

def orderedOrdinaryHubWeight (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (u:U)
    (W:OrderedOrdinaryWheel (U:=U) π b (m+1)):ℝ :=if W.2=u then w W else 0

theorem ordered_ordinary_hub_weight_nonneg
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (hw:∀W,0≤w W) (u:U) (W:OrderedOrdinaryWheel (U:=U) π b (m+1)):
    0≤orderedOrdinaryHubWeight w u W :=by
  unfold orderedOrdinaryHubWeight
  split_ifs <;> first | exact hw W | rfl

theorem ordered_ordinary_hub_weight_incidence_bound (hm:2≤m) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m) (u:U) (e:(V×V)⊕(V×U)):
    resourceFullIncidenceWeight orderedOrdinaryResources (orderedOrdinaryHubWeight w u) e≤((m:ℝ)+1)^2*B :=by
  apply (show resourceFullIncidenceWeight orderedOrdinaryResources (orderedOrdinaryHubWeight w u) e≤
      ∑W,if e∈orderedOrdinaryResources W then w W else 0 from ?_).trans
    (orderedOrdinary_root_load_bound hm hn hu w B hB hw e)
  unfold resourceFullIncidenceWeight
  apply Finset.sum_le_sum
  intro W _
  unfold orderedOrdinaryHubWeight
  split_ifs <;> first | exact le_refl _ | exact (hw W).1

theorem ordered_ordinary_hub_weight_total_bound (hm:2≤m) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m) (u:U):
    (∑W,orderedOrdinaryHubWeight w u W)≤(Fintype.card V:ℝ)*(((m:ℝ)+1)^2*B) :=by
  have hterm (W:OrderedOrdinaryWheel (U:=U) π b (m+1)):
      orderedOrdinaryHubWeight w u W≤∑v:V,if Sum.inr (v,u)∈orderedOrdinaryResources W then w W else 0:=by
    by_cases huW:W.2=u
    · let i:Fin (m+1):=⟨0,by omega⟩
      let v:=W.1.val i
      have hv:Sum.inr (v,u)∈orderedOrdinaryResources W:=by
        apply (orderedOrdinaryResources_spoke W (v,u)).2
        exact ⟨i,by simp only [v,huW]⟩
      have hh:=Finset.single_le_sum (s:=Finset.univ)
        (f:=fun v:V=>if Sum.inr (v,u)∈orderedOrdinaryResources W then w W else 0)
        (by intro v _;split_ifs <;> first | exact (hw W).1 | rfl) (Finset.mem_univ v)
      simpa only [orderedOrdinaryHubWeight,huW,ite_true,hv] using hh
    · have hh:0≤∑v:V,if Sum.inr (v,u)∈orderedOrdinaryResources W then w W else 0:=
        Finset.sum_nonneg (fun v _=>by split_ifs <;> first | exact (hw W).1 | rfl)
      simpa only [orderedOrdinaryHubWeight,huW,ite_false] using hh
  calc
    _ ≤ ∑W,∑v:V,if Sum.inr (v,u)∈orderedOrdinaryResources W then w W else 0:=
      Finset.sum_le_sum (fun W _=>hterm W)
    _ = ∑v:V,∑W,if Sum.inr (v,u)∈orderedOrdinaryResources W then w W else 0:=Finset.sum_comm
    _ ≤ ∑_v:V,((m:ℝ)+1)^2*B:=Finset.sum_le_sum (fun v _=>orderedOrdinary_root_load_bound hm hn hu w B hB hw (Sum.inr (v,u)))
    _ = _ :=by simp
end Oberwolfach
