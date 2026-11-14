import PerdidaDeLasCuatroCoordenadas
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte
noncomputable section

def coefTransicion (m l M C : ℝ≥0) :=
  (m^4+2*m)*(6*parMax (m^4) (m^4) l + 4*constanteUna l M C)

theorem perdida_media_en_el_estado {n h : ℕ} {p : FactoresContinuos} {κ m ζ z C E : ℝ≥0} {L : ℝ}
    (hn : 2≤n) (hh : h≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (m1 : 1≤m)
    (zp : 0<ζ) (hz : ζ≤z) (z1 : z≤1) (bal : BalanceMalla n h p C)
    (he : E/n≤piso κ ζ) (ho : 2*C/n≤piso κ ζ) (X : State n) (reg : Seguimiento h p X z E) (c : Coord) :
    let w:=coloresDelPerfil n h p
    let clk:=(↑(2*n-1):ℝ≥0)*z
    let B:=coefTransicion m (piso κ ζ) (techo m κ ζ) C
    within masas (avg masas (choices masas X w (·⁻¹)) (perdidaFisica X (vInicial p) w c))
      (observed masas (·⁻¹) (vInicial p) w X c*((ordenFisico c:ℝ≥0)*clk⁻¹)) (B*(E+1)/n) := by
  intro w clk B
  let A:=region_del_estado hn hh sp kp m1 zp hz z1 bal he ho X reg
  let D:=parMax (m^4) (m^4) (piso κ ζ)
  let S:=constanteUna (piso κ ζ) (techo m κ ζ) C
  have pos : 0<n := by omega
  have np : 0<(n:ℝ≥0) := by exact_mod_cast pos
  have cancel (a : ℝ≥0) : (n:ℝ≥0)*(a/n)≤a := le_of_eq (by field_simp)
  have tick : (n:ℝ≥0)⁻¹*A.time⁻¹=clk⁻¹ := by
    change _⁻¹*((((↑(2*n-1):ℝ≥0)/n)*z))⁻¹=(((↑(2*n-1):ℝ≥0)*z))⁻¹
    rw [←mul_inv,←mul_assoc]; congr 2; field_simp
  have big : margenSoporte D S E ≤ (6*D+4*S)*(E+1) := by
    calc _ ≤ margenSoporte D S E+6*D*E := le_add_of_nonneg_right (zero_le _)
         _ = _ := by unfold margenSoporte; ring
  have normBound (a : ℝ≥0) (h : a≤(n:ℝ≥0)*(m^4+2*m)) :
      a*(margenSoporte D S E/(n:ℝ≥0)^2)≤B*(E+1)/n := by
    calc _ ≤ ((n:ℝ≥0)*(m^4+2*m))*(((6*D+4*S)*(E+1))/(n:ℝ≥0)^2) :=
              mul_le_mul' h (div_le_div_of_nonneg_right big (zero_le _))
         _ = _ := by change _=((m^4+2*m)*(6*D+4*S))*(E+1)/n; field_simp; ring
  have gate:=deriva_de_un_soporte A pos E C (cancel E) (cancel (2*C)) (cancel C)
  cases c with
  | realCount =>
    have h:=perdida_media_real A
    change avg masas (choices masas X w (·⁻¹)) (perdidaFisica X (vInicial p) w .realCount)=_ at h
    rw [h,tick]
    simp only [ordenFisico,Nat.cast_one,one_mul,observed,ns_real]
    exact within_self masas _ _
  | family i =>
    have raw:=A.family_drift i (fun _ h => inv_mul_cancel₀ h) (fun _ h => le_antisymm h (zero_le _))
    simp only [ns_real] at raw
    change within masas _ (familiaN p h X i*((n:ℝ≥0)⁻¹*A.time⁻¹)) (familiaN p h X i*((n:ℝ≥0)⁻¹*A.combined)) at raw
    rw [tick] at raw
    simp only [ordenFisico,Nat.cast_one,one_mul]
    apply grow masas raw
    have a:=presupuesto_escalado A E C (cancel E) (cancel (2*C)) (cancel C)
    have b:=masa_virtual_acotada pos hh sp m1 X i
    calc _ ≤ ((n:ℝ≥0)*(2*m))*((n:ℝ≥0)⁻¹*A.combined) := mul_le_mul_right' b _
         _ = (2*m)*((n:ℝ≥0)*A.combined)/n := by field_simp; ring
         _ ≤ (2*m)*(S*(E+1))/n := div_le_div_of_nonneg_right (mul_le_mul_left' a _) (zero_le _)
         _ ≤ B*(E+1)/n := by
           apply div_le_div_of_nonneg_right _ (zero_le _)
           rw [←mul_assoc]; apply mul_le_mul_right'
           exact mul_le_mul' (le_add_self : 2*m≤m^4+2*m)
             (show S≤6*D+4*S from le_trans (by exact le_mul_of_one_le_left (zero_le _) (by norm_num : (1:ℝ≥0)≤4)) le_add_self)
  | degree j =>
    have raw:=gate (fun e => hitsVertex (lines e) j) (some j.1)
    dsimp only at raw
    rw [(identities masas X A.v j).2,tick] at raw
    apply grow masas raw
    apply normBound
    exact (grado_controlado_por_la_fibra p X j _ (cota_de_un_peso sp)).trans (mul_le_mul_left' le_self_add _)
  | boardWeight =>
    have raw:=gate (fun _ => true) none
    dsimp only at raw
    rw [(identities masas X A.v (0,0)).1,tick] at raw
    have scaled:=scale masas (n:ℝ≥0)⁻¹ raw
    simp only [ordenFisico,perdidaFisica,observed,Trayectoria.E2.Regular.norm,ns_real,avg_mul]
    rw [show A.v=vInicial p from rfl] at raw
    have outs : avg masas (choices masas X w (·⁻¹)) (perdidaFisica X (vInicial p) w .boardWeight) = (n:ℝ≥0)⁻¹ * avg masas _ (lostGate masas X (vInicial p) (fun _ => true) (families none)) := avg_mul masas _ _ _
    rw [outs]
    change within masas ((n:ℝ≥0)⁻¹*_) (((n:ℝ≥0)⁻¹*masaN p X)*(4*clk⁻¹)) _
    change within masas _ ((n:ℝ≥0)⁻¹*(masaN p X*(4*clk⁻¹))) ((n:ℝ≥0)⁻¹*(masaN p X*(margenSoporte D S E/(n:ℝ≥0)^2))) at scaled
    rw [←mul_assoc (n:ℝ≥0)⁻¹ (masaN p X) (4*clk⁻¹),←mul_assoc (n:ℝ≥0)⁻¹ (masaN p X) (margenSoporte D S E/(n:ℝ≥0)^2)] at scaled
    apply grow masas scaled; apply normBound
    have h:=mul_le_mul_left' (masa_viva_acotada X sp) (n:ℝ≥0)⁻¹
    calc _ ≤ _ := h
         _ = (n:ℝ≥0)*m^4 := by field_simp; ring
         _ ≤ _ := mul_le_mul_left' le_self_add _
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.perdida_media_en_el_estado
