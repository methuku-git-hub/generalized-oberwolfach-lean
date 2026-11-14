module

public import Oberwolfach.BalancedOrientation

@[expose] public section
/-! Convert matrix degree balances into cardinalities of the actual directed
physical arc set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def orientationMatrixArcs {V:Type} [Fintype V] (M:V→V→ℕ):Finset (V×V):=
  Finset.univ.filter (fun xy=>M xy.1 xy.2=1)

theorem balanced_orientation_arc_degrees
    {V:Type} [Fintype V] [DecidableEq V] (G:SimpleGraph V) (M:V→V→ℕ)
    (hphysical:∀x y,M x y+M y x=if G.Adj x y then 1 else 0):
    ∀v,((orientationMatrixArcs M).filter (fun xy=>xy.1=v)).card=∑w,M v w ∧
      ((orientationMatrixArcs M).filter (fun xy=>xy.2=v)).card=∑w,M w v:=by
  have hbound:∀x y,M x y≤1:=by
    intro x y
    have h:=hphysical x y
    split_ifs at h <;> omega
  have hcard:∀f:V→ℕ,(∀w,f w≤1)→(Finset.univ.filter (fun w=>f w=1)).card=∑w,f w:=by
    intro f hf
    calc
      (Finset.univ.filter (fun w=>f w=1)).card=∑w,if f w=1 then 1 else 0:=by simp
      _=∑w,f w:=by
        apply Finset.sum_congr rfl
        intro w _
        specialize hf w
        by_cases hw:f w=1 <;> simp [hw] <;> omega
  intro v
  have hout:(orientationMatrixArcs M).filter (fun xy=>xy.1=v)=
      (Finset.univ.filter (fun w=>M v w=1)).image (fun w=>(v,w)):=by
    ext ⟨x,y⟩
    simp [orientationMatrixArcs,eq_comm]
    intro h;subst_vars;rfl
  have hin:(orientationMatrixArcs M).filter (fun xy=>xy.2=v)=
      (Finset.univ.filter (fun w=>M w v=1)).image (fun w=>(w,v)):=by
    ext ⟨x,y⟩
    simp [orientationMatrixArcs,eq_comm]
    intro h;subst_vars;rfl
  rw [hout,hin,Finset.card_image_of_injective _ (fun _ _ h=>congrArg Prod.snd h),
    Finset.card_image_of_injective _ (fun _ _ h=>congrArg Prod.fst h)]
  exact ⟨hcard _ (fun w=>hbound v w),hcard _ (fun w=>hbound w v)⟩

theorem balanced_orientation_regular_target
    {V:Type} [Fintype V] (G:SimpleGraph V) (M:V→V→ℕ) (m:ℕ)
    (hregular:G.IsRegularOfDegree (2*m))
    (hbalanced:∀v,(∑w,M v w)=G.degree v/2 ∧ (∑w,M w v)=G.degree v/2):
    ∀v,(∑w,M v w)=m ∧ (∑w,M w v)=m:=by
  intro v
  have h:=hbalanced v
  have hreg:=hregular v
  rw [hreg] at h
  simpa using h

end Oberwolfach
