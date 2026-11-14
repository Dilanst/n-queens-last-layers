import ParadaDeLasReparacionesDirectas
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.Adjunto Trayectoria.ProfileKernel RealFinita Corte Repair
noncomputable section

def saltoDirecto (ζ P : ℝ≥0) :=
  let B:=masas.times 16 (oneMaskCap masas ζ⁻¹ P)
  B+B

theorem cola_de_candidatos_en_el_corte {n h T : ℕ} {p : FactoresContinuos} {κ m ζ C u : ℝ≥0} {L : ℝ}
    (hn : 2≤n) (hh : h≤n) (sp : ControlEspacial p κ m L) (kp : 0<κ) (m1 : 1≤m) (zp : 0<ζ)
    (tN : T≤2*n-1) (floor : ζ≤fraccionAntes n T) (bal : BalanceMalla n h p C) (mar : 2*(C:ℝ)≤κ*n)
    (he : u/n≤piso κ ζ) (ho : 2*C/n≤piso κ ζ) (z : Cell n)
    (θ a : ℝ) (tp : 0≤θ) (small : θ*(saltoDirecto ζ (m^4/κ^4):ℝ)≤1) :
    let x:ℕ×State n:=(0,initial n h)
    let S:=pasoDeRaiz h T p u
    let U:=constanteDirecta m κ ζ C*(u+1)/n
    let ini:=blancoDeLaRaiz ((T:ℝ≥0)/(↑(2*n-1):ℝ≥0)) z (cargaDeDestino h p z) (probDeLaCasilla h p)
    (avg masas (rutas S 0 T x) (mark masas (fun l =>
      let last:=l.foldl (fun _ y => y) x
      last.1=T ∧ a+T*(U:ℝ)≤|(physicalCount last.2.physical z:ℝ)-(ini:ℝ)|))).val ≤
      2*Real.exp ((T:ℝ)*(θ*(saltoDirecto ζ (m^4/κ^4):ℝ))^2-θ*a) := by
  intro x S U ini
  let N:=2*n-1
  let w:=coloresDelPerfil n h p
  let R:=parteDeRaiz p h T z
  let P:=m^4/κ^4
  let stop:=freezeAt T (pararRaiz (n:=n) h p u)
  have nn : 0<n := by omega
  have N0 : 0<N := by dsimp [N]; omega
  have nN : (n:ℝ≥0)≤(N:ℝ≥0) := by exact_mod_cast (show n≤N by dsimp [N]; omega)
  have npp : 0<(N:ℝ≥0) := by exact_mod_cast N0
  have margin : (n:ℝ≥0)*ζ≤(↑(N-T):ℝ≥0) := by
    apply (mul_le_mul_right' nN ζ).trans
    have cutoff : ζ≤(↑(N-T):ℝ≥0)/N := floor
    rw [mul_comm]; exact (le_div_iff₀ npp).mp cutoff
  have time : T<N := by
    apply lt_of_not_ge; intro nt; have eq : N-T=0 := Nat.sub_eq_zero_of_le nt
    rw [eq,Nat.cast_zero] at margin
    exact (not_lt_of_ge margin) (mul_pos (by exact_mod_cast nn) zp)
  have cap:=cargas_para_un_cruce hn sp kp bal mar z
  have rec (a : ℝ≥0) (ha : a≠masas.zero) : masas.mul a⁻¹ a=masas.one := inv_mul_cancel₀ ha
  have pos (i j : ℕ) (ne : i+j≠0) : masas.add (ns masas i) (ns masas j)≠masas.zero := by
    rw [ns_real,ns_real]; change (i:ℝ≥0)+j≠0; rw [←Nat.cast_add]; exact_mod_cast ne
  have norm:=stopped_total masas _ stop (kernel_total masas w (·⁻¹) rec pos)
  have tail:=cola_del_valor_en_buenas_historias S (R false) (R true) U (saltoDirecto ζ P)
    (fun (y : ℕ×State n) => coherent y.2) norm (coherent_at_stop masas w (·⁻¹) stop)
    (by
      intro t y good i hi
      exact (stopped_innovation masas (·⁻¹) rec pos w N T time (by dsimp [N]; omega)
        (by rw [ns_real]; change (n:ℝ≥0)≠0; exact_mod_cast nn.ne') ζ P zp.ne' (by simpa only [ns_real] using margin)
        z (cargaDeDestino h p z) (probDeLaCasilla h p) (by simpa only [ns_real] using cap.2) cap.1
        (pararRaiz h p u) t y.1 y.2 good).2 i hi) 0 T x (initial_coherent n h) θ a tp small
  apply le_trans _ tail
  apply NNReal.coe_le_coe.mpr
  apply misma_masa_en_el_soporte
  intro i mem nz yes
  have len:=(pasos_con_peso mem nz).1
  let last:=i.2.foldl (fun _ y => y) x
  obtain ⟨reached,bad⟩:=yes
  change last.1=T at reached
  refine ⟨len,presupuesto_de_toda_historia hn hh sp kp m1 zp tN floor bal mar he ho z i.2 0 x,?_⟩
  have iniEq : (R false x).val-(R true x).val=ini := by
    simpa only [R,x,parteDeRaiz,Nat.sub_zero,valorDeRaiz] using
      inicio_de_la_raiz h N T N0 tN z (cargaDeDestino h p z) (probDeLaCasilla h p) cap.1
  have endEq : (R false last).val-(R true last).val=physicalCount last.2.physical z := by
    dsimp only [R,parteDeRaiz]; rw [reached,Nat.sub_self]
    exact fin_de_la_raiz_en_el_corte N (N-T) z _ _ last.2
  change a+T*(U:ℝ)≤|((R false last).val-(R true last).val)-((R false x).val-(R true x).val)|
  rwa [iniEq,endEq]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.cola_de_candidatos_en_el_corte
