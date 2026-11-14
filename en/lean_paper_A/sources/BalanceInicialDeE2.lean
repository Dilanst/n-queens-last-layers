import GradosDeLasCuatroLineas
import CondicionesDelPerfilKL
open Set MeasureTheory
open scoped BigOperators NNReal
namespace ArticuloA.Historias
open Perfil Trayectoria Trayectoria.E2
noncomputable section

def Wfisico (n : ℕ) (p : FactoresContinuos) := ∑ e : Cell n,pesoFisico n p e
def cargaLinea (n q : ℕ) (p : FactoresContinuos) (i : Fin 4) (j : Indice n) :=
  (q:ℝ)*gradoInicial n p i j/Wfisico n p
def cargaCelda (n q : ℕ) (p : FactoresContinuos) (e : Cell n) :=
  (q:ℝ)*pesoFisico n p e/Wfisico n p

theorem masa_fisica_reescalada (n : ℕ) (p : FactoresContinuos) :
    Wfisico n p=muestraTablero n (pesoContinuo p) := by
  unfold Wfisico pesoFisico muestraTablero
  rw [Fintype.sum_prod_type]; simp_rw [Finset.sum_range]; simp only [centro,nodo,zero_add,medio]

theorem masa_inferior {n : ℕ} {p κ M L} (data : ControlEspacial p κ M L) (kpos : 0≤κ) :
    κ^4*(n:ℝ)^2≤Wfisico n p := by
  calc
    _ = ∑ _e : Cell n,κ^4 := by simp [Fintype.card_prod,nsmul_eq_mul]; ring
    _ ≤ _ := Finset.sum_le_sum (fun e _ => (limites_del_producto data kpos _ _ (medio_admisible e.1.isLt)
      (medio_admisible e.2.isLt)).1)

theorem cuadratura_total_fisica {n : ℕ} {p κ M L} (hn : 0<n) (data : ControlEspacial p κ M L) (mp : 0≤M) (lp : 0≤L) :
    |Wfisico n p-(n:ℝ)^2*integralTablero (pesoContinuo p)|≤2*(4*M^3*L)*n := by
  rw [masa_fisica_reescalada,abs_sub_comm]
  apply cuadratura_dos_dimensiones n hn (pesoContinuo p) _ (by positivity)
  · intro r hr s hs j hj
    simpa only [sub_self,abs_zero,add_zero] using variacion_del_peso data lp r s j j hr hs hj hj
  · intro r hr c hc j hj
    simpa only [sub_self,abs_zero,zero_add] using variacion_del_peso data lp r r c j hr hr hc hj

theorem balance_inicial_E2 {n q : ℕ} {p κ M L} (hn : 0<n) (qn : q≤n) (data : ControlEspacial p κ M L)
    (kp : 0<κ) (mp : 0≤M) (lp : 0≤L) (b : ℝ) (bp : 0<b)
    (masa : integralTablero (pesoContinuo p)=((q:ℝ)/n)/b)
    (i : Fin 4) (j : Indice n) (u : ℝ) (u0 : 0≤u) (u1 : u≤1)
    (euler : b*integralLinea p n j.val i=1-u) :
    (n:ℝ)*|cargaLinea n q p i j+u-1|≤(4*(4*M^3*L))/κ^4 := by
  let D:=Wfisico n p/(n:ℝ)^2
  let r:=(q:ℝ)/(n:ℝ)
  let J:=integralLinea p n j.val i
  let e:= (Wfisico n p-(n:ℝ)^2*integralTablero (pesoContinuo p))/n
  let g:=gradoInicial n p i j-(n:ℝ)*J
  let C:=4*M^3*L
  have np : 0<(n:ℝ) := by exact_mod_cast hn
  have den : κ^4≤D := (le_div_iff₀ (pow_pos np 2)).mpr (masa_inferior data kp.le)
  have sum := cuadratura_total_fisica hn data mp lp
  have eb : |e|≤2*C := by
    dsimp only [e]; rw [abs_div,abs_of_pos np]; exact (div_le_iff₀ np).mpr sum
  have main := balance_de_fibra n r b D J u e g (2*C) (2*C) (κ^4) np bp (pow_pos kp _) den
    (div_nonneg (Nat.cast_nonneg _) np.le) ((div_le_one np).mpr (by exact_mod_cast qn)) u0 u1
    (by dsimp only [D,r,e]; rw [masa]; field_simp; ring) euler eb (cuadratura_grado_inicial hn data mp lp i j)
  have w0 : 0<Wfisico n p := (mul_pos (pow_pos kp _) (pow_pos np 2)).trans_le (masa_inferior data kp.le)
  have eq : r*(J+g/(n:ℝ))/D=cargaLinea n q p i j := by
    unfold cargaLinea; dsimp only [D,r,g]; field_simp; ring
  rw [eq] at main
  simpa only [show 2*C+2*C=4*C by ring,C] using main

theorem arista_difusa {n q : ℕ} {p κ M L} (hn : 0<n) (qn : q≤n) (data : ControlEspacial p κ M L)
    (kp : 0<κ) (e : Cell n) : (n:ℝ)*cargaCelda n q p e≤M^4/κ^4 := by
  have np : 0<(n:ℝ) := by exact_mod_cast hn
  have low:=masa_inferior (n:=n) data kp.le
  have w0:0<Wfisico n p:=(mul_pos (pow_pos kp _) (pow_pos np 2)).trans_le low
  have lohi:=limites_del_producto data kp.le _ _ (medio_admisible e.1.isLt) (medio_admisible e.2.isLt)
  have hi : (q:ℝ)*pesoFisico n p e≤(n:ℝ)*M^4 :=
    mul_le_mul (by exact_mod_cast qn) lohi.2 ((pow_nonneg kp.le 4).trans lohi.1) np.le
  unfold cargaCelda; rw [←mul_div_assoc,div_le_div_iff₀ w0 (pow_pos kp 4)]
  calc
    _ ≤ ((n:ℝ)*(n*M^4))*κ^4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi np.le) (pow_nonneg kp.le _)
    _ = M^4*(κ^4*(n:ℝ)^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left low (by positivity)
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.balance_inicial_E2
#print axioms ArticuloA.Historias.arista_difusa
