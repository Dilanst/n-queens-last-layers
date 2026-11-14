import CambioDeLasDosDiagonalesDeDestino
open scoped NNReal BigOperators
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section
open Classical

private theorem producto_tres {u v w x y z : ℝ} (vp : 0≤v) (xp : 0≤x) (yp : 0≤y)
    (wp : 0≤w) (w1 : w≤1) :
    |u*v*w-x*y*z|≤|u-x| *v+x*|v-y|+x*y*|w-z| := by
  have id : u*v*w-x*y*z=((u-x)*v*w+x*(v-y)*w)+x*y*(w-z) := by ring
  rw [id]
  apply (abs_add_le _ _).trans
  apply add_le_add
  · apply (abs_add_le _ _).trans
    simp only [abs_mul,abs_of_nonneg vp,abs_of_nonneg xp,abs_of_nonneg wp]
    exact add_le_add (mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) vp) w1)
      (mul_le_of_le_one_right (mul_nonneg xp (abs_nonneg _)) w1)
  · simp [abs_mul,abs_of_nonneg xp,abs_of_nonneg yp]

def patronEscalado {n} (X : State n) (t : CuatroMarcas) (u : Mark n) : ℝ :=
  masaFuente X t.1 u.1*masaFuente X t.2.1 u.2*ambasMarcas X (corners u).2 t.2.2.1 t.2.2.2

theorem suma_cambios_del_patron {n} (hn : 0<n) (X : State n) (a : Choice n) (good : coherent X)
    (ok : allowed X a) (t : CuatroMarcas) :
    (∑ u : Mark n,|patronEscalado (next X a) t u-patronEscalado X t u|)≤10*n := by
  let Y:=next X a
  let s:=fun (X' : State n) => masaFuente X' t.1
  let f:=fun (X' : State n) => masaFuente X' t.2.1
  let d:=fun (X' : State n) z => ambasMarcas X' z t.2.2.1 t.2.2.2
  let ds:=fun e => |s Y e-s X e|
  let df:=fun e => |f Y e-f X e|
  let dd:=fun z => |d Y z-d X z|
  have one (u : Mark n) :
      |patronEscalado Y t u-patronEscalado X t u|≤ds u.1*f Y u.2+s X u.1*df u.2+
        s X u.1*f X u.2*dd (corners u).2 := producto_tres
      (masaFuente_no_negativa _ _ _) (masaFuente_no_negativa _ _ _) (masaFuente_no_negativa _ _ _)
      (escalar_no_negativo _) (escalar_a_lo_sumo_uno _)
  have fresh:=choice_adm good a ok
  have Yleg := (next_coherent good a ok).1
  have prod (b c : Cell n→ℝ) : (∑ u : Mark n,b u.1*c u.2)=(∑ e,b e)*(∑ e,c e) := by
    rw [Fintype.sum_prod_type,Finset.sum_mul]
    simp only [Finset.mul_sum]
  have first : (∑ u : Mark n,ds u.1*f Y u.2)≤4*(n:ℝ) := by
    rw [prod]; exact mul_le_mul (cambio_total_de_fuente hn X a fresh _) (masa_total_de_fuente Yleg _)
      (Finset.sum_nonneg (fun e _ => masaFuente_no_negativa _ _ e)) (by norm_num)
  have second : (∑ u : Mark n,s X u.1*df u.2)≤(n:ℝ)*4 := by
    rw [prod]; exact mul_le_mul (masa_total_de_fuente good.1 _) (cambio_total_de_fuente hn X a fresh _)
      (Finset.sum_nonneg (fun e _ => abs_nonneg _)) (Nat.cast_nonneg _)
  have last : (∑ u : Mark n,s X u.1*f X u.2*dd (corners u).2)≤2*n :=
    (masa_de_un_cruce_marcado good.1 good.1 _ _ dd (fun _ => abs_nonneg _)).trans
      (coste_de_las_dos_diagonales X a fresh _ _)
  apply (Finset.sum_le_sum (fun u _ => one u)).trans
  simp only [Finset.sum_add_distrib]
  linarith only [first,second,last]

theorem identidad_del_patron_escalado {n} (X : State n) (t : CuatroMarcas) (u : Mark n) :
    patronEscalado X t u=(escalaDelPatron n t:ℝ)*
      estadoEscalar (patronInverso X u.1 u.2 t.1 t.2.1 t.2.2.1 t.2.2.2) := by
  have mult (P Q : Prop) : estadoEscalar (P∧Q)=estadoEscalar P*estadoEscalar Q := by
    by_cases h:P <;> by_cases g:Q <;> simp [estadoEscalar,indicator,h,g]
  unfold patronEscalado escalaDelPatron masaFuente ambasMarcas patronInverso
  simp only [mult,NNReal.coe_mul]; dsimp only [banderaDeLinea,estadoMarca]; ring

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.suma_cambios_del_patron
#print axioms ArticuloA.Historias.identidad_del_patron_escalado
