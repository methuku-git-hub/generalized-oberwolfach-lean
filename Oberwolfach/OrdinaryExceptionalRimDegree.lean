module

public import Oberwolfach.OrdinaryExceptionalColourDegrees
public import Oberwolfach.OrdinarySampleReferenceActiveContainment

@[expose] public section
/-! Simultaneous colour counts bound the exceptional graph left by the
ordinary reference-versus-matching comparison. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_exceptional_rim_degree_bound
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (p k p₂ k₂ u t δ:ℝ) (hk:0≤k) (hk₂:0≤k₂) (hu:0≤u)
    (hdegree:∀a x,|(sampledColourDegree P (fun e=>(σ (Sum.inl e)).1) a x:ℝ)-
      markedExpandedPhysicalProbability p k p₂ k₂ u a*P.degree x|<t)
    (hDel:∀x,(Del.degree x:ℝ)≤δ):
    let Except:=(((longPhysicalStateGraph P σ {1}⊔longPhysicalStateGraph P σ {3})⊔longPhysicalStateGraph P σ {4})⊔
      (permutationConflictGraph π (3*d+2)⊔Del));
    ∀x,(Except.degree x:ℝ)≤(2*k+2*k₂+u)*n+3*t+(6*d+4:ℕ)+δ:=by
  intro Except x
  let A:=longPhysicalStateGraph P σ {1}
  let B:=longPhysicalStateGraph P σ {3}
  let C:=longPhysicalStateGraph P σ {4}
  let D:=permutationConflictGraph π (3*d+2)
  obtain ⟨hA,hB,hC⟩:=ordinary_exceptional_colour_degree_bounds P σ p k p₂ k₂ u t hk hk₂ hu hdegree
  have h1:((Except.degree x):ℝ)≤(((A⊔B)⊔C).degree x:ℝ)+(D⊔Del).degree x:=by
    have hn:Except.degree x≤((A⊔B)⊔C).degree x+(D⊔Del).degree x:=by
      have hh:=graph_degree_sup_le ((A⊔B)⊔C) (D⊔Del) x
      convert hh using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
    exact_mod_cast hn
  have h2:((((A⊔B)⊔C).degree x):ℝ)≤((A⊔B).degree x:ℝ)+C.degree x:=by
    have hn:((A⊔B)⊔C).degree x≤(A⊔B).degree x+C.degree x:=by
      have hh:=graph_degree_sup_le (A⊔B) C x
      convert hh using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
    exact_mod_cast hn
  have h3:(((A⊔B).degree x):ℝ)≤(A.degree x:ℝ)+B.degree x:=by
    exact_mod_cast graph_degree_sup_le A B x
  have h4:(((D⊔Del).degree x):ℝ)≤(D.degree x:ℝ)+Del.degree x:=by
    exact_mod_cast graph_degree_sup_le D Del x
  have h5:(D.degree x:ℝ)≤(6*d+4:ℕ):=by
    have hn:D.degree x≤6*d+4:=by
      have hh:=permutationConflictGraph_degree_le π (3*d+2) x
      have hh':D.degree x≤2*(3*d+2):=by
        convert hh using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
      omega
    exact_mod_cast hn
  linarith [hA x,hB x,hC x,hDel x]
end Oberwolfach
