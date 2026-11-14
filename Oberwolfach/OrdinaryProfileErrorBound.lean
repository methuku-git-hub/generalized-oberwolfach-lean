module

public import Oberwolfach.OrdinaryProfileFailureMargins
public import Oberwolfach.OrdinaryProfileCardinalityBounds

@[expose] public section
/-! Actual root and pair counts make the two profile-event failure terms small. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem ordinary_profile_error_bound (r d:ℕ) (hr:2≤r) (b t ρ:ℝ)
    (hb:0<b) (ht:0<t) (hρ:0<ρ):
    ∃ N:ℕ,∀ (V U:Type) [Fintype V] [Fintype U],N≤Fintype.card V→
      Fintype.card U≤Fintype.card V →
    let n:ℝ:=Fintype.card V
    let C:ℝ:=2*(4*(d:ℝ)+3)
    let errD:=(Fintype.card (U×U):ℝ)*(Fintype.card (Sym2 V⊕(V×Unit)):ℝ)*
      (2*Real.exp (-2*t^2/(C^2*((r:ℝ)^4*(4*b)/n)*(2*r)*((r:ℝ)^2*(4*b)))))
    let errR:=(Fintype.card V+1:ℝ)^2*(Fintype.card U+1:ℝ)^2*
      (2*Real.exp (-2*(ρ*n)^2/((4*(d:ℝ)+3)^2*(2*(2*(2:ℝ)+1)*n))));
    errD+errR≤2/n^2 := by
  have hrR:(0:ℝ)<r:=by exact_mod_cast (show 0<r by omega)
  let A:ℝ:=(2*(4*(d:ℝ)+3))^2*((r:ℝ)^4*(4*b))*(2*r)*((r:ℝ)^2*(4*b))
  let B:ℝ:=(4*(d:ℝ)+3)^2*(2*(2*(2:ℝ)+1))
  have hA:0<A:=by dsimp [A];positivity
  have hB:0<B:=by dsimp [B];positivity
  obtain ⟨N,hN⟩:=ordinary_profile_failure_margins A B t ρ hA hB ht hρ
  refine ⟨max 1 N,?_⟩
  intro V U _ _ hn hu n C errD errR
  have hn1:1≤Fintype.card V:=by omega
  have hnN:N≤Fintype.card V:=by omega
  have hc:=ordinary_profile_cardinality_bounds (V:=V) (U:=U) hn1 hu
  have hh:=hN (Fintype.card V) hnN
    ((Fintype.card (U×U):ℝ)*(Fintype.card (Sym2 V⊕(V×Unit)):ℝ))
    ((Fintype.card V+1:ℝ)^2*(Fintype.card U+1:ℝ)^2)
    (by positivity) hc.1 (by positivity) hc.2
  have hden:C^2*((r:ℝ)^4*(4*b)/n)*(2*r)*((r:ℝ)^2*(4*b))=A/n:=by dsimp [C,A];ring
  have hrow:(4*(d:ℝ)+3)^2*(2*(2*(2:ℝ)+1)*n)=B*n:=by dsimp [B];ring
  change _+_≤2/n^2 at hh
  dsimp only [errD,errR]
  rw [hden,hrow]
  exact hh
end Oberwolfach
