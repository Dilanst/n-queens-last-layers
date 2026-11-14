import MediaExteriorDeLaInversa
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical
open Perfil
def masaTransversal {n} (h : ℕ) (p : FactoresContinuos) (col : Bool) (z : Fin n) :=
  ∑ i : Fin n,(probDeLaCasilla h p (if col then (i,z) else (z,i)):ℝ)

theorem suma_sin_peso_por_marginales {n} (h : ℕ) (p : FactoresContinuos) :
    sumaInversaDeLosCentros (n:=n) h p (fun _ => 1)=
      ∑ z : Cell n,psiEnElCentro p z*masaTransversal h p false z.1*masaTransversal h p true z.2 := by
  let π := fun e : Cell n => (probDeLaCasilla h p e:ℝ)
  let f := fun u : Mark n => psiEnElCentro p u.2*(π (u.1.1,u.2.2)*π (u.2.1,u.1.2))
  let perm : Mark n≃Mark n := ⟨corners,corners,fun _ => rfl,fun _ => rfl⟩
  have eq : sumaInversaDeLosCentros (n:=n) h p (fun _ => 1)=∑ u : Mark n,f (perm u) := by
    unfold sumaInversaDeLosCentros
    apply Finset.sum_congr rfl; rintro ⟨⟨r,j⟩,i,c⟩ _
    dsimp [f,π,perm,corners]; ring
  rw [eq,Equiv.sum_comp perm f,Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  rintro ⟨i,j⟩ _
  rw [Fintype.sum_prod_type]
  dsimp only [f,π,masaTransversal,Bool.false_eq_true,ite_false,ite_true]
  simp_rw [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl; intro r _
  apply Finset.sum_congr rfl; intro c _
  simp; ring

theorem balance_de_una_transversal {n h} {p : FactoresContinuos} {κ M L : ℝ} {C : ℝ≥0}
    (hn : 0<n) (sp : ControlEspacial p κ M L) (bal : BalanceMalla n h p C)
    (col : Bool) (z : Fin n) : |masaTransversal h p col z-1|≤((C:ℝ)+h*M)/n := by
  let j : Indice n := ⟨z.val,by have :=z.isLt; change z.val<2*n-1; omega⟩
  let f : Fin 4 := if col then 1 else 0
  have nr : 0<(n:ℝ) := by exact_mod_cast hn
  have js : j.val<n := z.isLt
  have id : masaTransversal h p col z=cargaLinea n (n-h) p f j := by
    unfold masaTransversal cargaLinea
    rw [suma_transversal p col j js]
    simp_rw [probabilidad_fisica_por_peso p hn]
    rw [Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl; intro i _
    cases col <;> simp [trazaTransversal,pesoFisico,j] <;> ring
  have slack : |holguraInicial n h p f j|≤((h:ℝ)*M)/n := by
    rw [virtual_de_la_malla]
    have one {y : ℝ≥0} (bd : (y:ℝ)≤M) : |((fraccionHuecos n h*y:ℝ≥0):ℝ)|≤((h:ℝ)*M)/n := by
      change |((h:ℝ)/n)*(y:ℝ)|≤_
      rw [abs_of_nonneg (show 0≤((h:ℝ)/n)*(y:ℝ) by positivity),div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left bd (Nat.cast_nonneg _)) nr.le
    cases col <;> simp only [f,Bool.false_eq_true,ite_false,ite_true,factores,pesosMalla,if_pos js]
    · exact one (sp.Rmax _ (medio_admisible z.isLt))
    · exact one (sp.Cmax _ (medio_admisible z.isLt))
  have base : |cargaLinea n (n-h) p f j+holguraInicial n h p f j-1|≤(C:ℝ)/n :=
    (le_div_iff₀ nr).mpr (by simpa only [mul_comm] using bal f j)
  rw [id,show cargaLinea n (n-h) p f j-1=(cargaLinea n (n-h) p f j+holguraInicial n h p f j-1)-holguraInicial n h p f j by ring]
  simpa only [add_div] using (abs_sub _ _).trans (add_le_add base slack)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.suma_sin_peso_por_marginales
#print axioms ArticuloA.Historias.balance_de_una_transversal
