module

public import Oberwolfach.PrescribedPackingUnion
public import Oberwolfach.OrdinaryWheelRemainders

@[expose] public section

/-! Exact local inputs left by the prescribed-inner-edge wheel packing.
Balance is needed only at the indicated roots, rather than at all vertices
of the temporarily excluded comparison host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Z:Type} [Fintype V] [Fintype U] [Fintype Z] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

theorem ordinary_decomposition_remainder_row_balance_at (R:SimpleGraph V) (K:V→U→Prop)
    (hRQ:R≤Q) (hKH:∀ v u,K v u→H v u)
    (hdec:HasOrdinaryWheelDecomposition R K r) (v:V)
    (hbal:Q.degree v=2*(Finset.univ.filter (H v)).card):
    (Q\R).degree v=2*(Finset.univ.filter (fun u=>H v u∧¬K v u)).card:=by
  have hR:=(ordinary_wheel_decomposition_balance R K r hdec).1 v
  rw [graph_degree_sdiff Q R hRQ,hbal,hR,spoke_row_sdiff_card H K hKH v,Nat.mul_sub_left_distrib]

theorem ordinary_decomposition_remainder_hub_divisibility_at (R:SimpleGraph V) (K:V→U→Prop)
    (hKH:∀ v u,K v u→H v u)
    (hdec:HasOrdinaryWheelDecomposition R K r) (u:U)
    (hdiv:r∣(Finset.univ.filter (fun v=>H v u)).card):
    r∣(Finset.univ.filter (fun v=>H v u∧¬K v u)).card:=by
  have hK:=(ordinary_wheel_decomposition_balance R K r hdec).2 u
  rw [spoke_col_sdiff_card H K hKH u]
  exact Nat.dvd_sub hdiv hK

theorem prescribed_cover_root_geometry (C:Z→OrdinaryWheel Q F H r)
    (I:Finset V) (J:Finset U) (T:Finset V) (W:Finset U)
    (E₀:Finset (Sym2 V⊕(V×U)))
    (hcovered:E₀⊆ordinaryHostResources (wheelFamilyRim C) (wheelFamilySpokes C))
    (hrim:∀ x∈T,∀ y∈I,Q.Adj x y→Sum.inl s(x,y)∈E₀)
    (hrow:∀ x∈T,∀ u∈J,H x u→Sum.inr (x,u)∈E₀)
    (hcol:∀ u∈W,∀ x∈I,H x u→Sum.inr (x,u)∈E₀):
    (∀ x∈T,(Q\wheelFamilyRim C).neighborFinset x⊆Finset.univ\I) ∧
    (∀ x∈T,∀ u,H x u∧¬wheelFamilySpokes C x u→u∈Finset.univ\J) ∧
    (∀ u∈W,Finset.univ.filter (fun v=>H v u∧¬wheelFamilySpokes C v u)⊆Finset.univ\I):=by
  refine ⟨?_,?_,?_⟩
  · intro x hx y hy
    obtain ⟨hQ,hnot⟩:=((Q\wheelFamilyRim C).mem_neighborFinset x y).mp hy
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
    intro hyI
    have he:=hcovered (hrim x hx y hyI hQ)
    exact hnot ((ordinaryHostResources_rim (wheelFamilyRim C) (wheelFamilySpokes C) s(x,y)).mp he)
  · intro x hx u hu
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
    intro huJ
    have he:=hcovered (hrow x hx u huJ hu.1)
    exact hu.2 ((ordinaryHostResources_spoke (wheelFamilyRim C) (wheelFamilySpokes C) x u).mp he)
  · intro u hu x hx
    obtain ⟨hH,hnot⟩:=(Finset.mem_filter.mp hx).2
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
    intro hxI
    have he:=hcovered (hcol u hu x hxI hH)
    exact hnot ((ordinaryHostResources_spoke (wheelFamilyRim C) (wheelFamilySpokes C) x u).mp he)

theorem prescribed_wheel_family_root_balance (C:Z→OrdinaryWheel Q F H r)
    (hdis:∀ i j,i≠j→Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j)))
    (T:Finset V) (W:Finset U)
    (hbal:∀ x∈T,Q.degree x=2*(Finset.univ.filter (H x)).card)
    (hdiv:∀ u∈W,r∣(Finset.univ.filter (fun v=>H v u)).card):
    (∀ x∈T,(Q\wheelFamilyRim C).degree x=
      2*(Finset.univ.filter (fun u=>H x u∧¬wheelFamilySpokes C x u)).card) ∧
    (∀ u∈W,r∣(Finset.univ.filter (fun v=>H v u∧¬wheelFamilySpokes C v u)).card):=by
  have hdec:=wheelFamily_decomposition C hdis
  have hsub:=wheelFamily_subhost C
  exact ⟨fun x hx=>ordinary_decomposition_remainder_row_balance_at (wheelFamilyRim C)
      (wheelFamilySpokes C) hsub.1 hsub.2 hdec x (hbal x hx),
    fun u hu=>ordinary_decomposition_remainder_hub_divisibility_at (wheelFamilyRim C)
      (wheelFamilySpokes C) hsub.2 hdec u (hdiv u hu)⟩

end Oberwolfach
