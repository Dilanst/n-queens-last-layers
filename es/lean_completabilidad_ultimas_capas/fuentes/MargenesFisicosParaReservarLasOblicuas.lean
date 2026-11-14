import FibrasDeLaCuadraturaEnLaReserva
import BalanceUniformeParaElNumeroDeHuecosVariable
namespace ArticuloA.Historias
open Repair Perfil Trayectoria Trayectoria.E2 Real Filter Set
open scoped NNReal BigOperators Topology
noncomputable section
open Classical

theorem margenes_fisicos_de_la_reserva (κ M L : ℝ) (kp : 0<κ) (k1 : κ≤1)
    (mm : 1≤M) (lp : 0≤L) :
    ∀ᶠ n : ℕ in atTop, ∀ {P p b},EulerFisica P p (fraccionHuecos n (huecosReserva n)) b →
      ControlEspacial p κ M L →
      let w:=cargaCelda n (n-huecosReserva n) p
      (∀ i : Bool×Fin n,masaBajo w (enLaFibra (.inl i))≤1-κ*fraccionReserva n/2) ∧
      (∀ j : LineaReservable n,masaBajo w (enLaFibra (.inr j))≤1-3*κ/4) := by
  let C:=4*(4*M^3*L)/κ^4
  have small:=fraccion_de_reserva_tiende_a_cero.eventually_lt_const (by norm_num : (0:ℝ)<1/2)
  filter_upwards [cortes_de_la_reserva,eventually_ge_atTop 1,small,
    la_reserva_supera_cualquier_umbral_de_huecos (2*C/κ),
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (4*C/κ)] with n cut hn half mh nh
  intro P p b eu reg w
  have np : 0<(n:ℝ):=by exact_mod_cast hn
  have eps : 0≤fraccionReserva n:=by unfold fraccionReserva; positivity
  have me:= (div_le_iff₀ kp).mp mh
  have ne:= (div_le_iff₀ kp).mp nh
  have rc : C/(n:ℝ)≤κ*fraccionReserva n/2 := by
    apply (div_le_iff₀ np).mpr
    have eq : κ*fraccionReserva n/2*n=κ*(huecosReserva n:ℝ)/2 := by
      unfold fraccionReserva
      field_simp; ring
    rw [eq]
    linarith only [me]
  have ob : C/(n:ℝ)≤κ/4 := by
    apply (div_le_iff₀ np).mpr
    linarith only [ne]
  have main (i : FibraDeB1 n) (z : Cell n) (hz : enLaFibra i z) :
      masaBajo w (enLaFibra i) ≤ 1-(if (familiaDeReserva i).val<2 then fraccionReserva n else 1)*κ+C/n := by
    let a:=familiaDeReserva i
    let j : Indice n:=⟨lines z a,rango z a⟩
    have fis : a.val<2 → j.val<n := by
      intro h
      have r:=z.1.isLt
      have c:=z.2.isLt
      change lines z a<n
      have opts : a=0 ∨ a=1 := by omega
      rcases opts with h0|h1
      · rw [h0]; exact r
      · rw [h1]; exact c
    have u:=holgura_muestreada_de_la_linea (h:=huecosReserva n) hn reg a j fis
    have d:=discrepancia_de_linea_para_h_variable hn cut.2.1 eu reg kp (zero_le_one.trans mm) lp a j
    have ub : cargaLinea n (n-huecosReserva n) p a j+holguraInicial n (huecosReserva n) p a j-1≤C/n :=
      (le_abs_self _).trans ((le_div_iff₀ np).mpr (by simpa [C,mul_comm] using d))
    have ex : (fraccionHuecos n (huecosReserva n):ℝ)=fraccionReserva n:=by simp [fraccionHuecos,fraccionReserva]
    rw [ex] at u
    change masaBajo (cargaCelda n (n-huecosReserva n) p) _≤_
    rw [carga_sobre_una_fibra_fisica _ _ _ z hz]
    change cargaLinea n (n-huecosReserva n) p a j≤_
    linarith only [u,ub]
  constructor
  · rintro ⟨b',t⟩
    by_cases pres : ∃ z : Cell n,enLaFibra (.inl (b',t)) z
    · obtain ⟨z,hz⟩:=pres
      have h:=main _ z hz
      cases b' <;> simp [familiaDeReserva] at h <;> linarith only [rc,h]
    · rw [masa_nula_de_fibra_vacia w _ pres]
      have ub:=mul_le_mul_of_nonneg_right k1 eps
      linarith
  · rintro ⟨b',t⟩
    by_cases pres : ∃ z : Cell n,enLaFibra (.inr (b',t)) z
    · obtain ⟨z,hz⟩:=pres
      have h:=main _ z hz
      cases b' <;> simp [familiaDeReserva,show ¬(3:Fin 4).val<2 by decide] at h <;> linarith only [ob,h]
    · rw [masa_nula_de_fibra_vacia w _ pres]
      linarith
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.margenes_fisicos_de_la_reserva
