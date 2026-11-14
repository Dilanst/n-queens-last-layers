import BalanceEscaladoDeLaMalla
import MargenUniformeAntesDelCorte
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte
noncomputable section

/-- The four deviations observed immediately before a step; the auxiliary degree
ignores activation of its own vertex. This event is not asserted for every path. -/
structure Seguimiento {n} (h : ℕ) (p : FactoresContinuos) (X : State n) (z E : ℝ≥0) : Prop where
  reloj : (↑(X.reals+X.virtuals):ℝ≥0)=(↑(2*n-1):ℝ≥0)*z
  piezas : within masas ((X.reals:ℝ≥0)/n) (cuotaR n h*z) (E/n)
  grados : ∀ j,activeLine X j → within masas (gradoN p X j/n) (gradoIni n h p j*z^3) (E/n)
  masa : within masas (masaN p X/(n:ℝ≥0)^2) (totalIni n h p*z^4) (E/n)
  virtual : ∀ i,within masas (familiaN p h X i/n) (famIni n h p i*z) (E/n)

theorem cubo_numerico (z : ℝ≥0) : cube masas z=z^3 := by change (z*z)*z=_; ring
theorem cuarta_numerica (z : ℝ≥0) : fourth masas z=z^4 := by change ((z*z)*z)*z=_; ring

def region_del_estado {n h : ℕ} {p : FactoresContinuos} {κ m ζ z C E : ℝ≥0} {L : ℝ}
    (hn : 2≤n) (hh : h≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (m1 : 1≤m)
    (zp : 0<ζ) (hz : ζ≤z) (z1 : z≤1) (bal : BalanceMalla n h p C)
    (he : E/n≤piso κ ζ) (ho : 2*C/n≤piso κ ζ)
    (X : State n) (reg : Seguimiento h p X z E) : Region masas X (coloresDelPerfil n h p) (·⁻¹) := by
  have pos : 0<n := by omega
  have np : 0<(n:ℝ≥0) := by exact_mod_cast pos
  have lp:=piso_positivo kp zp
  have margins:=margenes_del_reloj (h:=h) hn sp hz z1 _ _ he ho
  have clk:=margins.1
  have clk4:=margins.2.1
  have clk2:=margins.2.2.1
  have flW:=margins.2.2.2.1
  have flU:=margins.2.2.2.2
  have caps:=techos_comunes m κ ζ
  have m2:=caps.1
  have mpow:=caps.2.1
  have mm:=caps.2.2.1
  have mload:=caps.2.2.2.1
  have mvirt:=caps.2.2.2.2
  have rq:=(cotas_reloj_y_cuotas hn h).2.2.1
  have sum:=(cotas_reloj_y_cuotas hn h).2.2.2.2
  have qv : cuotaV n h*z≤relojIni n*z := mul_le_mul_right' (sum ▸ le_add_self) z
  have vcap (i : Fin 4) (k : ℕ) (ok : k<2*n-1) := cap_virtual_fisico pos hh sp m1 i ⟨k,ok⟩
  have wpos := (pow_pos kp 4).trans_le (suelo_total_fisico (h:=h) pos sp)
  have wne : Wfisico n p≠0 := ((mul_pos (pow_pos (show 0<(κ:ℝ) by exact_mod_cast kp) 4)
    (pow_pos (show 0<(n:ℝ) by exact_mod_cast pos) 2)).trans_le (masa_inferior sp κ.property)).ne'
  have clkEq : timeMass masas X=(↑(2*n-1):ℝ≥0)*z := by
    simpa only [timeMass,ns_real,Nat.cast_add] using reg.reloj
  have timeN : norm masas (·⁻¹) (ns masas n) (timeMass masas X)=relojIni n*z := by
    rw [clkEq,ns_real]; change _⁻¹*(_*z)=(_/_)*z; rw [div_eq_mul_inv]; ac_rfl
  have capRatio (x y t : ℝ≥0) (top : x≤y) (low : piso κ ζ≤t) : t⁻¹*x≤y/piso κ ζ := by
    rw [mul_comm,←div_eq_mul_inv]; exact div_le_div₀ (zero_le _) top lp low
  refine {
    v:=vInicial p, common:=factorRealN n h, z:=z, c:=relojIni n, w₀:=totalIni n h p, d₀:=gradoIni n h p,
    u₀:=famIni n h p, q₀:=cuotaR n h, h₀:=cuotaV n h, p:=probLinea n h p, piN:=probArista n h p,
    eps:=E/n, off:=2*C/n, bal:=C/n, l:=piso κ ζ, M:=techo m κ ζ, mr:=m^4, mv:=m^4,
    wt:=factor_real_del_color p, sizePos:=by rw [ns_real]; exact np.ne', commonPos:=(factor_real_positivo pos).ne',
    floorPos:=lp.ne', running:=?_, clock:=timeN, clockPos:=(lp.trans_le clk).ne', sourceClock:=?_,
    low:=clk, high:=clk2.trans m2, clockFrac:=z1, initial:=?_, trackQ:=?_, trackD:=?_, trackW:=?_, trackU:=?_,
    offset:=offset_regional pos wne bal, balance:=?_, wMargin:=?_, uMargin:=flU, load:=?_, cellLoad:=?_,
    degreeMax:=?_, weightMax:=cota_de_un_peso sp, cellMax:=mpow, tupleMax:=?_, vertexMax:=?_, qMax:=?_,
    hMax:=qv.trans (clk2.trans m2), pMax:=?_, uMax:=?_, piMax:=?_ }
  · intro eq; rw [eq] at timeN
    change (ns masas n)⁻¹*0=_ at timeN; rw [mul_zero] at timeN
    exact (lp.trans_le clk).ne' timeN.symm
  · rw [cuarta_numerica]; exact (lp.trans_le clk4).ne'
  · change _*z+_*z=_*z; rw [←add_mul,sum]
  · rw [ns_real,ns_real]; change within masas ((n:ℝ≥0)⁻¹*_) _ _; rw [inv_mul_eq_div]; exact reg.piezas
  · intro j hv; rw [ns_real,cubo_numerico]; change within masas ((n:ℝ≥0)⁻¹*gradoN p X j) _ _
    rw [inv_mul_eq_div]; exact reg.grados j hv
  · rw [ns_real,cuarta_numerica]; change within masas (((n:ℝ≥0)*n)⁻¹*masaN p X) _ _
    rw [inv_mul_eq_div,←pow_two]; exact reg.masa
  · intro i; rw [ns_real]; change within masas ((n:ℝ≥0)⁻¹*familiaN p h X i) _ _
    rw [inv_mul_eq_div]; exact reg.virtual i
  · intro j live; exact balance_regional pos bal j.1 ⟨j.2,live.1⟩
  · rw [cuarta_numerica]; exact flW
  · intro j; change totalIni n h p*(_/totalIni n h p)=_; field_simp; rfl
  · intro e; change totalIni n h p*(_/totalIni n h p)=_; field_simp; rfl
  · intro j _; rw [ns_real]; change (n:ℝ≥0)⁻¹*gradoN p X j≤_
    simpa only [div_eq_mul_inv,mul_comm] using (grado_normalizado_acotado (h:=h) pos sp X j).1.trans mpow
  · exact fun g mem _ => peso_tupla_controlado _ m vcap g mem
  · exact fun j hj => (vcap j.1 j.2 hj.1).trans mm
  · exact (mul_le_mul' rq z1).trans (by simpa only [one_mul] using (le_trans (by norm_num : (1:ℝ≥0)≤2) m2))
  · intro j _; exact (capRatio _ _ _ (cargas_acotadas hn sp kp j (⟨0,pos⟩,⟨0,pos⟩)).1 clk).trans mload
  · intro j hj; exact (capRatio _ _ _ (vcap j.1 j.2 hj.1) clk).trans mvirt
  · intro e; rw [cuarta_numerica]
    exact (capRatio _ _ _ (cargas_acotadas hn sp kp (0,0) e).2 clk4).trans mload
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.region_del_estado
