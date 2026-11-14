import EulerPuntualEnLasCuatroFamilias
import EscalaDeReservaDeN3A2
namespace ArticuloA.Historias
open Perfil Real Set Filter
open scoped NNReal Topology
noncomputable section

/-- Euler y el balance se aplican al h propio de cada tablero, con la misma constante. -/
theorem discrepancia_de_linea_para_h_variable {n h : ℕ} {P p b κ M L}
    (hn : 0<n) (hh : h≤n) (e : EulerFisica P p (fraccionHuecos n h) b)
    (sp : ControlEspacial p κ M L) (kp : 0<κ) (mp : 0≤M) (lp : 0≤L)
    (i : Fin 4) (j : Indice n) :
    (n:ℝ)*|cargaLinea n (n-h) p i j+holguraInicial n h p i j-1|≤4*(4*M^3*L)/κ^4 := by
  have np : 0<(n:ℝ):=by exact_mod_cast hn
  have mass:=integral_masa_cuadrada e
  have eq : 1-(fraccionHuecos n h:ℝ)=(↑(n-h):ℝ)/n := by
    simp only [fraccionHuecos,NNReal.coe_div,NNReal.coe_natCast,Nat.cast_sub hh]
    field_simp
  rw [e.masa,eq] at mass
  have point (j : Fin 4) : ∀ t∈rangoF j,b*integralFisica p j t=1-holguraLinea p (fraccionHuecos n h) j t := by
    fin_cases j
    · exact integral_euler_en_rectas e sp lp 0 (by decide)
    · exact integral_euler_en_rectas e sp lp 1 (by decide)
    · exact euler_oblicua_puntual e sp lp false
    · exact euler_oblicua_puntual e sp lp true
  apply balance_desde_euler_continua hn sp kp mp lp e.coef mass point _ i j
  intro f t ht
  linarith only [point f t ht,mul_nonneg e.coef.le (integral_fisica_no_negativa p f t ht)]

theorem la_reserva_supera_cualquier_umbral_de_huecos (C : ℝ) :
    ∀ᶠ n : ℕ in atTop,C≤(huecosReserva n:ℝ) := by
  have big : Tendsto (fun n : ℕ=>(n:ℝ)^(1-4*exponenteReserva)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num [exponenteReserva])).comp tendsto_natCast_atTop_atTop
  filter_upwards [big.eventually_ge_atTop (8000*(C+1))] with n hn
  have floor:=Nat.lt_floor_add_one ((1/8000:ℝ)*(n:ℝ)^(1-4*exponenteReserva))
  unfold huecosReserva
  linarith

theorem holgura_muestreada_de_la_linea {n h : ℕ} {p κ M L} (hn : 0<n)
    (sp : ControlEspacial p κ M L) (i : Fin 4) (j : Indice n) (fis : i.val<2 → j.val<n) :
    (if i.val<2 then (fraccionHuecos n h:ℝ) else 1)*κ≤holguraInicial n h p i j := by
  have pos:=indice_en_intervalo hn i j fis
  have lower:=(regular_familia sp i).minimo _ pos
  rw [virtual_de_la_malla]
  fin_cases i <;> simp [factores,pesosMalla,posicionLinea,factorF,fis] at lower ⊢
  all_goals first | exact mul_le_mul_of_nonneg_left lower (by positivity) | exact lower

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.discrepancia_de_linea_para_h_variable
#print axioms ArticuloA.Historias.holgura_muestreada_de_la_linea
