module

public import Oberwolfach.OrdinaryFullHostLoadMargins

@[expose] public section
/-! Polynomial counts of the roots and two-hub tests. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem ordinary_profile_cardinality_bounds {V U:Type} [Fintype V] [Fintype U]
    (hn:1≤Fintype.card V) (hu:Fintype.card U≤Fintype.card V):
    (Fintype.card (U×U):ℝ)*(Fintype.card (Sym2 V⊕(V×Unit)):ℝ)≤2*(Fintype.card V:ℝ)^4 ∧
    (Fintype.card V+1:ℝ)^2*(Fintype.card U+1:ℝ)^2≤16*(Fintype.card V:ℝ)^4 := by
  have hnR:(1:ℝ)≤Fintype.card V:=by exact_mod_cast hn
  have huR:(Fintype.card U:ℝ)≤Fintype.card V:=by exact_mod_cast hu
  have hres:(Fintype.card (Sym2 V⊕(V×Unit)):ℝ)≤2*(Fintype.card V:ℝ)^2:=by
    have hh:=ordinary_resource_domain_card (V:=V) (U:=Unit) (by simpa using hn)
    exact_mod_cast hh
  have hu2:(Fintype.card (U×U):ℝ)≤(Fintype.card V:ℝ)^2:=by
    rw [Fintype.card_prod]
    have hh:=Nat.mul_le_mul hu hu
    have hhR:(Fintype.card U:ℝ)*Fintype.card U≤(Fintype.card V:ℝ)*Fintype.card V:=by exact_mod_cast hh
    simpa only [Nat.cast_mul,pow_two] using hhR
  constructor
  · calc
      _ ≤ (Fintype.card V:ℝ)^2*(2*(Fintype.card V:ℝ)^2):=
        mul_le_mul hu2 hres (by positivity) (by positivity)
      _ = _ := by ring
  · have hnplus:(Fintype.card V+1:ℝ)≤2*Fintype.card V:=by linarith
    have huplus:(Fintype.card U+1:ℝ)≤2*Fintype.card V:=by linarith
    calc
      _ ≤ (2*(Fintype.card V:ℝ))^2*(2*(Fintype.card V:ℝ))^2 := by gcongr
      _ = _ := by ring
end Oberwolfach
