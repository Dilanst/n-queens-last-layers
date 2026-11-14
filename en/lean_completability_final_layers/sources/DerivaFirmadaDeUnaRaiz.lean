import PresupuestoDeLaRaizFisica
open scoped NNReal
namespace ArticuloA.Historias
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel Trayectoria.Adjunto RealFinita Corte
noncomputable section

def masaDeCasilla {n} {X : State n} {w} (A : Region masas X w (·⁻¹)) (e : Cell n) := A.piN e / n

set_option maxHeartbeats 600000 in
theorem deriva_de_raiz_en_la_region {n} {X : State n} {w} (A : Region masas X w (·⁻¹))
    (nn : 0<n) (coh : coherent X) (vivo : X.failed=false) (enCurso : X.reals+X.virtuals≠0)
    (E C P ζ : ℝ≥0) (he : n*A.eps≤E) (ho : n*A.off≤2*C) (hb : n*A.bal≤C)
    (t N m d : ℕ) (fits : d≤m) (step : m+1≤N) (span : N≤2*n) (zp : 0<ζ)
    (fl : (n:ℝ≥0)*ζ≤m) (clk : (N:ℝ≥0)*A.z=(↑(m+1):ℝ≥0))
    (span' : (n:ℝ≥0)*A.c=N) (z : Cell n) (hp : ∀ e j,A.p (side j,key z e j)≤1)
    (pc : ∀ e,A.piN e≤P) :
    let R := fun m d y j => rootPart masas (·⁻¹) N m d z (fun e i => A.p (side i,key z e i)) (masaDeCasilla A) y j
    let row := kernel masas w (·⁻¹) t X
    within masas (avg masas row (fun y => R m d y false)+R (m+1) (d+1) X true)
      (avg masas row (fun y => R m d y true)+R (m+1) (d+1) X false)
      (cotaDeRaiz (constanteUna A.l A.M C) (A.mr/A.l+4*(A.mv/A.l^4)) P ζ*(E+1)/n) := by
  intro R row
  have np : 0<(n:ℝ≥0) := by exact_mod_cast nn
  have rec (u : ℝ≥0) (nz : u≠masas.zero) : masas.mul u⁻¹ u=masas.one := inv_mul_cancel₀ nz
  have pos (i j : ℕ) (ne : i+j≠0) : masas.add (ns masas i) (ns masas j)≠masas.zero := by
    rw [ns_real,ns_real]; change (i:ℝ≥0)+j≠0; rw [←Nat.cast_add]; exact_mod_cast ne
  have pre : 0<(m:ℝ≥0) := (mul_pos np zp).trans_le fl
  have mp : ns masas m≠masas.zero := by rw [ns_real]; exact pre.ne'
  have mp' : ns masas (m+1)≠masas.zero := by rw [ns_real]; change (↑(m+1):ℝ≥0)≠0; positivity
  let W := P/n*cube masas (N:ℝ≥0)
  have mass (e : Cell n) : A.piN e=masas.mul (ns masas n) (masaDeCasilla A e) := by
    rw [ns_real]; change _=n*(A.piN e/n); field_simp
  have major (e : Cell n) : masas.le (masas.mul (masaDeCasilla A e) (cube masas (ns masas N))) W := by
    rw [ns_real]; exact mul_le_mul_right' (div_le_div_of_nonneg_right (pc e) (zero_le _)) _
  have src:=board_step masas A coh coh.1 rec (fun _ h => le_antisymm h (zero_le _)) pos vivo enCurso t N m d
    fits step mp mp' (n*ζ) (mul_pos np zp).ne' (by rw [ns_real]; exact fl) z hp
    (by rw [ns_real,ns_real]; exact span') (by rw [ns_real,ns_real]; exact clk) _ mass W major
  apply grow masas src
  let a := ((n:ℝ≥0)*ζ)⁻¹
  let K := W*quart masas a
  let V := (N:ℝ≥0)*K
  let pair := ((n:ℝ≥0)^2)⁻¹*(A.mr/A.l+4*(A.mv/A.l^4))
  let b := (n:ℝ≥0)⁻¹*A.combined
  let g := ((n:ℝ≥0)^2)⁻¹*A.budget
  have nums:=scale_caps masas (·⁻¹) rec n N (P/n) ζ P (by rw [ns_real]; exact np.ne') zp.ne' span
    (by rw [ns_real]; change (n:ℝ≥0)*(P/n)≤P; apply le_of_eq; field_simp)
  simp only [ns_real] at nums
  let H := 8*P*ζ⁻¹^4
  have eqH : ((P*cube masas (2:ℝ≥0))*quart masas ζ⁻¹)=H := by
    change _=8*P*ζ⁻¹^4; change (P*((2*2)*2))*((ζ⁻¹*ζ⁻¹)*(ζ⁻¹*ζ⁻¹))=_; ring
  have two : (↑(2:ℕ):ℝ≥0)=2 := by norm_num
  have kval:=nums.2.1
  change (n:ℝ≥0)*n*K≤P*cube masas (↑(2:ℕ):ℝ≥0)*quart masas ζ⁻¹ at kval
  rw [two,eqH,←pow_two] at kval
  have vbd:=nums.2.2
  change (n:ℝ≥0)*V≤(↑(2:ℕ):ℝ≥0)*(P*cube masas (↑(2:ℕ):ℝ≥0)*quart masas ζ⁻¹) at vbd
  rw [two,eqH] at vbd
  obtain ⟨_,_,bb,gg,_,_⟩:=errores_de_los_patrones A nn coh E C he ho hb z z (fun _ => false)
  have pp : (n:ℝ≥0)^2*pair≤A.mr/A.l+4*(A.mv/A.l^4) := by dsimp [pair]; field_simp
  have bd:=presupuesto_en_unidades_de_raiz n b g pair V a K _ _ H ζ⁻¹ E bb gg pp vbd nums.1.le kval
  apply (le_div_iff₀ np).mpr
  rw [mul_comm]
  have four : masas.four (fun _ => A.l)=A.l^4 := by change (A.l*A.l)*(A.l*A.l)=_; ring
  simp only [ns_real,four]
  have pair_eq : ((n:ℝ≥0)*n)⁻¹*(A.l⁻¹*A.mr+masas.times 4 ((A.l^4)⁻¹*A.mv))=pair := by
    rw [times_m,ns_real]; change _*(A.l⁻¹*A.mr+(↑(4:ℕ):ℝ≥0)*((A.l^4)⁻¹*A.mv))=pair
    dsimp only [pair]; norm_num only [Nat.cast_ofNat]; rw [pow_two]; simp only [div_eq_mul_inv]; ring
  change n*(masas.times 16 (fwCap masas n b (((n:ℝ≥0)*n)⁻¹*A.budget)
    (((n:ℝ≥0)*n)⁻¹*(A.l⁻¹*A.mr+masas.times 4 ((A.l^4)⁻¹*A.mv))) V)+
    masas.times 16 (masas.times n (occupiedCap masas a)+masas.times (n*n) (availCap masas a V K)))≤_
  rw [pair_eq,←pow_two]
  exact bd

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.deriva_de_raiz_en_la_region
