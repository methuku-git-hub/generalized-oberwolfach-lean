module

public import Oberwolfach.TypedCycleClassLoads

@[expose] public section

/-! Original marked cycle coefficients after changing fixed classes.
The error uses the ambient order n and is uniform over all typed roots;
only the final conversion to a degree sum requires the root to be present. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem class_load_scale_bound (m:ℕ) (hm:1≤m) (n L J B:ℝ)
    (hn:1≤n) (hL:0≤L) (hJ:0≤J) (hB:0≤B):
    L*J*(2*n+1)^(m-1)*(B/n^m)≤(J*3^(m-1)*B)*L/n:=by
  have hn0:0<n:=lt_of_lt_of_le (by norm_num) hn
  have hp:(2*n+1)^(m-1)≤(3*n)^(m-1):=
    pow_le_pow_left₀ (by positivity) (by linarith) (m-1)
  calc
    _ ≤ L*J*(3*n)^(m-1)*(B/n^m):=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
    _ = _:=by
      rw [mul_pow]
      have he:n^m=n^(m-1)*n:=by
        rw [←pow_succ, Nat.sub_add_cancel hm]
      rw [he]
      field_simp
      <;> ring

variable {V E K:Type} [Fintype V] [DecidableEq V]
    {tail head:E→V} {ktail khead:K→V} {m:ℕ} {π:Equiv.Perm V} {b:ℕ}

 theorem typed_class_load_change_normalized (hm:1≤m) (hn:1≤Fintype.card V)
    (w:MarkedCycleTuple tail head ktail khead m π b→ℝ) (B₀:ℝ) (hB:0≤B₀)
    (hw:∀ C,0≤w C∧w C≤B₀/(Fintype.card V:ℝ)^m) (A B A' B':Finset V) (j:Bool) (v:V):
    |resourceRootOmittedLoad typedMarkedCycleVertices w (fun x=>x∈typedClassSet A B) (j,v)-
      resourceRootOmittedLoad typedMarkedCycleVertices w (fun x=>x∈typedClassSet A' B') (j,v)|≤
      (((m+1)^(m+1):ℕ):ℝ)*3^(m-1)*B₀*
        (((changed A A').card:ℝ)+(changed B B').card)/(Fintype.card V:ℝ):=by
  have hh:=typed_class_load_change hm w (B₀/(Fintype.card V:ℝ)^m) (by positivity) hw A B A' B' j v
  exact hh.trans (class_load_scale_bound m hm (Fintype.card V)
    (((changed A A').card:ℝ)+(changed B B').card) ((m+1)^(m+1):ℕ) B₀
    (by exact_mod_cast hn) (by positivity) (by positivity) hB)

 theorem class_weight_degree_stability (hm:1≤m) (hn:1≤Fintype.card V)
    (w:MarkedCycleTuple tail head ktail khead m π b→ℝ) (B₀ ε:ℝ) (hB:0≤B₀)
    (hw:∀ C,0≤w C∧w C≤B₀/(Fintype.card V:ℝ)^m) (A₀ B₀' A B:Finset V)
    (hAB:Disjoint A B)
    (herr:∀ j:Bool,∀ v:V,|1-resourceRootOmittedLoad typedMarkedCycleVertices w
      (fun x=>x∈typedClassSet A₀ B₀') (j,v)|≤ε):
    ∀ v∈A∪B,|1-hypergraphWeightedDegree classMarkedCycleVertices
      (fun C:ClassMarkedCycle tail head ktail khead m π b A B=>w (classMarkedCycleAsMarked C)) v|≤
        ε+(((m+1)^(m+1):ℕ):ℝ)*3^(m-1)*B₀*
          (((changed A₀ A).card:ℝ)+(changed B₀' B).card)/(Fintype.card V:ℝ):=by
  intro v hv
  have hcase:∃ j:Bool,if j then v∈A else v∈B:=by
    rcases Finset.mem_union.mp hv with hv|hv
    · exact ⟨true,hv⟩
    · exact ⟨false,hv⟩
  obtain ⟨j,hj⟩:=hcase
  rw [typed_class_degree_eq_omitted hAB w j v hj]
  have hh:=typed_class_load_change_normalized hm hn w B₀ hB hw A₀ B₀' A B j v
  calc
    _ ≤ |1-resourceRootOmittedLoad typedMarkedCycleVertices w (fun x=>x∈typedClassSet A₀ B₀') (j,v)|+
      |resourceRootOmittedLoad typedMarkedCycleVertices w (fun x=>x∈typedClassSet A₀ B₀') (j,v)-
        resourceRootOmittedLoad typedMarkedCycleVertices w (fun x=>x∈typedClassSet A B) (j,v)|:=abs_sub_le _ _ _
    _ ≤ _:=add_le_add (herr j v) hh

end Oberwolfach
