module

public import Oberwolfach.SelectedHubFactorWheels
public import Oberwolfach.OrdinaryExactDecomposition

@[expose] public section

/-! The two-factor hub switch in the ordinary transformer. Both sides
use the actual same rim factors. Their only difference is the specified
spokes at the added root set; all physical incidences are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {T:Finset V} {r:ℕ}

theorem selected_factor_hub_decomposition (M:Finset (LocalOrdinaryCycle Q F T r))
    (A:Finset V) (u:U)
    (hM:∀ C∈M,∀ C'∈M,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C'))
    (hA:M.biUnion localOrdinaryVertices=A) (hH:∀ v∈A,H v u):
    HasOrdinaryWheelDecomposition (localOrdinaryFactorGraph M) (fun v z=>v∈A∧z=u) r:=by
  let j:Unit↪U:=⟨fun _=>u,fun _ _ _=>Subsingleton.elim _ _⟩
  obtain ⟨W,_hW,hWr,hWs,_hdis,hdec⟩:=selected_hub_factor_wheels Q F H r
    (fun _:Unit=>T) (fun _:Unit=>A) j (fun _:Unit=>M) (fun _=>hM) (fun _=>hA)
    (fun _=>hH) (fun a b h=>False.elim (h (Subsingleton.elim a b)))
  have hrim:wheelFamilyRim W=localOrdinaryFactorGraph M:=hWr.trans (by simp)
  have hspoke:wheelFamilySpokes W=(fun v z=>v∈A∧z=u):=by
    funext v z
    apply propext
    rw [hWs]
    constructor
    · rintro ⟨_,hz,hv⟩;exact ⟨hv,hz.symm⟩
    · rintro ⟨hv,hz⟩;exact ⟨(),hz.symm,hv⟩
  rwa [hrim,hspoke] at hdec

theorem ordinary_hub_factor_trade (A Z:Finset V) (hAZ:Disjoint A Z) (u u':U) (hu:u≠u')
    (M₀ M₁:Finset (LocalOrdinaryCycle Q F T r))
    (h₀:(∀ C∈M₀,∀ D∈M₀,C≠D→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices D)) ∧
      M₀.biUnion localOrdinaryVertices=A)
    (h₁:(∀ C∈M₁,∀ D∈M₁,C≠D→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices D)) ∧
      M₁.biUnion localOrdinaryVertices=A∪Z)
    (hdis:Disjoint (localOrdinaryFactorGraph M₀) (localOrdinaryFactorGraph M₁))
    (hH:∀ v∈A∪Z,H v u∧H v u'):
    let R:=localOrdinaryFactorGraph M₁⊔localOrdinaryFactorGraph M₀
    let Splus:V→U→Prop:=fun v z=>(v∈A∪Z∧z=u)∨(v∈A∧z=u')
    let Sminus:V→U→Prop:=fun v z=>(v∈A∪Z∧z=u')∨(v∈A∧z=u)
    HasOrdinaryWheelDecomposition R Splus r ∧ HasOrdinaryWheelDecomposition R Sminus r ∧
    R≤Q ∧ (∀ v z,Splus v z→H v z) ∧ (∀ v z,Sminus v z→H v z) ∧
    (∀ e:Sym2 V⊕(V×U),
      (if e∈ordinaryHostResources R Splus then (1:ℤ) else 0)-
      (if e∈ordinaryHostResources R Sminus then 1 else 0)=
      (if e∈Z.image (fun v=>Sum.inr (v,u)) then 1 else 0)-
      (if e∈Z.image (fun v=>Sum.inr (v,u')) then 1 else 0)):=by
  dsimp only
  have h0u:=selected_factor_hub_decomposition (H:=H) M₀ A u h₀.1 h₀.2
    (fun v hv=>(hH v (Finset.mem_union_left _ hv)).1)
  have h0u':=selected_factor_hub_decomposition (H:=H) M₀ A u' h₀.1 h₀.2
    (fun v hv=>(hH v (Finset.mem_union_left _ hv)).2)
  have h1u:=selected_factor_hub_decomposition (H:=H) M₁ (A∪Z) u h₁.1 h₁.2 (fun v hv=>(hH v hv).1)
  have h1u':=selected_factor_hub_decomposition (H:=H) M₁ (A∪Z) u' h₁.1 h₁.2 (fun v hv=>(hH v hv).2)
  refine ⟨ordinary_wheel_decomposition_union _ _ _ _ r h1u h0u' hdis.symm
    (fun _ _ h=>hu (h.1.2.symm.trans h.2.2)),
    ordinary_wheel_decomposition_union _ _ _ _ r h1u' h0u hdis.symm
      (fun _ _ h=>hu (h.2.2.symm.trans h.1.2)),?_,?_,?_,?_⟩
  · have hle (M:Finset (LocalOrdinaryCycle Q F T r)):localOrdinaryFactorGraph M≤Q:=by
      intro a b hab
      obtain ⟨C,_hC,hC⟩:=(localOrdinaryFactorGraph_adj M a b).mp hab
      exact C.val.property hC
    exact sup_le (hle M₁) (hle M₀)
  · intro v z h
    rcases h with ⟨hv,rfl⟩|⟨hv,rfl⟩
    · exact (hH v hv).1
    · exact (hH v (Finset.mem_union_left _ hv)).2
  · intro v z h
    rcases h with ⟨hv,rfl⟩|⟨hv,rfl⟩
    · exact (hH v hv).2
    · exact (hH v (Finset.mem_union_left _ hv)).1
  · intro e
    cases e with
    | inl e=>simp only [ordinaryHostResources_rim,Finset.mem_image,Sum.inr_ne_inl,and_false,exists_false,ite_false,sub_self]
    | inr vz=>
      rcases vz with ⟨v,z⟩
      have hmem (a:U):(Sum.inr (v,z):Sym2 V⊕(V×U))∈Z.image (fun v=>Sum.inr (v,a))↔v∈Z∧z=a:=by
        simp only [Finset.mem_image,Sum.inr.injEq,Prod.mk.injEq]
        constructor
        · rintro ⟨v',hv',rfl,hz⟩;exact ⟨hv',hz.symm⟩
        · rintro ⟨hv,hz⟩;exact ⟨v,hv,rfl,hz.symm⟩
      simp only [ordinaryHostResources_spoke,hmem,Finset.mem_union]
      have hvdis:¬(v∈A∧v∈Z):=fun h=>Finset.disjoint_left.mp hAZ h.1 h.2
      have hzdis:¬(z=u∧z=u'):=fun h=>hu (h.1.symm.trans h.2)
      by_cases ha:v∈A <;> by_cases hz:v∈Z <;> by_cases hu0:z=u <;> by_cases hu1:z=u' <;>
        simp_all only [true_or,or_true,false_or,or_false,true_and,and_true,false_and,and_false,
          not_true_eq_false,not_false_eq_true,ite_true,ite_false] <;> omega

end Oberwolfach
