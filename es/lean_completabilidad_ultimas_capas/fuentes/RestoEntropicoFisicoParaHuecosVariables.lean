import CostoDeEntropiaRelativaDeLasHolguras
namespace ArticuloA.Historias
open Perfil Filter Real
open scoped BigOperators NNReal Topology
noncomputable section

private theorem compara_dos_holguras {u v d : ℝ} (up : 0<u) (bd : 2*d≤u) (diff : |v-u|≤d) :
    0<v ∧ v≤2*u := by
  have sides:=abs_le.mp diff
  constructor <;> linarith only [up,bd,sides.1,sides.2]

theorem correccion_entropica_de_las_lineas_fisicas (κ M L : ℝ) (kp : 0<κ) (k1 : κ≤1)
    (mm : 1≤M) (lp : 0≤L) :
    ∀ᶠ n : ℕ in atTop, ∀ {P p b},EulerFisica P p (fraccionHuecos n (huecosReserva n)) b →
    ControlEspacial p κ M L →
    let h:=huecosReserva n
    (∑ i,∑ j : Indice n,(1-cargaLinea n (n-h) p i j)*
      (log (1-cargaLinea n (n-h) p i j)-log (holguraInicial n h p i j)))≤16*(4*(4*M^3*L)/κ^4) := by
  let C:=4*(4*M^3*L)/κ^4
  have mp:=zero_le_one.trans mm
  have cp : 0≤C:=by dsimp [C]; positivity
  filter_upwards [eventually_ge_atTop 1,cortes_de_la_reserva,
    la_reserva_supera_cualquier_umbral_de_huecos (2*C/κ),
    fraccion_de_reserva_tiende_a_cero.eventually_lt_const zero_lt_one] with n hn cut big small
  intro P p b e reg h
  have np : 0<(n:ℝ):=by exact_mod_cast hn
  let x:=fraccionReserva n
  have xp : 0<x := div_pos (by exact_mod_cast (show 0<huecosReserva n from cut.1)) np
  have ex : (fraccionHuecos n h:ℝ)=x:=by simp [h,x,fraccionReserva,fraccionHuecos]
  have budget : 2*(C/n)≤κ*x := by
    have co: 2*C≤(huecosReserva n:ℝ)*κ:=(div_le_iff₀ kp).mp big
    change _≤κ*((huecosReserva n:ℝ)/n)
    simpa only [mul_div_assoc,mul_comm (huecosReserva n:ℝ) κ] using
      (div_le_div_of_nonneg_right co np.le)
  apply resto_total_de_holguras_muestreadas hn C cp
  intro i j u v
  have lo : κ*x≤u := by
    by_cases fis : i.val<2 → j.val<n
    · have floor:=holgura_muestreada_de_la_linea (h:=h) hn reg i j fis
      rw [ex] at floor
      by_cases ij : i.val<2
      · simpa [ij,mul_comm,u] using floor
      · have k:=mul_le_mul_of_nonneg_left small.le kp.le
        simp only [if_neg ij,one_mul] at floor
        linarith only [floor,k]
    · push_neg at fis
      have idx : i=0 ∨ i=1:=by omega
      have cutj : ¬j.val<n:=by omega
      have one : u=1 := by
        dsimp [u]; rw [virtual_de_la_malla]
        rcases idx with rfl|rfl <;> simp [factores,pesosMalla,cutj]
      rw [one]
      exact (mul_le_mul_of_nonneg_left small.le kp.le).trans (by simpa using k1)
  have up : 0<u:=(mul_pos kp xp).trans_le lo
  have dif:=discrepancia_de_linea_para_h_variable hn cut.2.1 e reg kp mp lp i j
  have dv : |v-u|≤C/n:=by
    apply (le_div_iff₀ np).mpr
    have eq : v-u= -(cargaLinea n (n-h) p i j+u-1):=by dsimp [v]; ring
    rw [eq,abs_neg,mul_comm]
    exact dif
  have pair:=compara_dos_holguras up (budget.trans lo) dv
  exact ⟨up,pair.1,pair.2,dv⟩
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.correccion_entropica_de_las_lineas_fisicas
