import FluctuacionesFisicasDeTableroMarcasYLineas
namespace ArticuloA.Historias
open Real
noncomputable section

theorem presupuesto_de_resto_y_saltos {n q η ν : ℝ} (qp : 0<q) (qn : q≤n) (hp : 0<η)
    (h1 : η≤1) (vp : 1≤ν) :
    let T:=ν/η^4
    let κ:=(5/4)/(η*q)
    let pm:=(ν/n/η^4)/((9/10)*q)
    let Bw:=4*n*(ν/n/η^4)
    let Bz:=(11/10)*(6*(1/(η*q)))+3*(ν/n/η^3)
    (100*κ^2+6*pm)*q^2≤164*T ∧ Bw≤4*T ∧ Bz*q≤10*T := by
  let T:=ν/η^4
  have np:=qp.trans_le qn
  have vn : 0≤ν:=by linarith
  have tn : 0≤T:=by dsimp [T]; positivity
  have e2 : η^4≤η^2:=pow_le_pow_of_le_one hp.le h1 (by omega)
  have e1 : η^4≤η^1:=pow_le_pow_of_le_one hp.le h1 (by omega)
  have e3 : η^4≤η^3:=pow_le_pow_of_le_one hp.le h1 (by omega)
  have b1 : 1/η≤T:=div_le_div₀ vn vp (pow_pos hp _) (by simpa using e1)
  have b2 : 1/η^2≤T:=div_le_div₀ vn vp (pow_pos hp _) e2
  have b3 : ν/η^3≤T:=div_le_div_of_nonneg_left vn (pow_pos hp _) e3
  have ratio : q/n≤1:=(div_le_one np).mpr qn
  
  dsimp only
  have r : (100*((5/4)/(η*q))^2+6*(ν/n/η^4/((9/10)*q)))*q^2=
        (625/4)*(1/η^2)+(20/3)*(q/n)*T:=by dsimp [T]; field_simp; ring
  have z : ((11/10)*(6*(1/(η*q)))+3*(ν/n/η^3))*q=(33/5)*(1/η)+3*((q/n)*(ν/η^3)):=by
    field_simp; ring
  have wr : 4*n*(ν/n/η^4)=4*T:=by dsimp [T]; field_simp; ring
  have r1 : (q/n)*T≤T:=by simpa using mul_le_mul_of_nonneg_right ratio tn
  have r3 : (q/n)*(ν/η^3)≤T:=by
    calc _ ≤ 1*(ν/η^3):=mul_le_mul_of_nonneg_right ratio (by positivity)
         _ ≤ T:=by simpa using b3
  change _≤164*T ∧ _≤4*T ∧ _≤10*T
  rw [r,z,wr]
  refine ⟨?_,le_rfl,?_⟩ <;> linarith only [tn,b1,b2,r1,r3]

theorem presupuesto_de_la_envolvente {q T a R Bw Bz : ℝ} (q1 : 1≤q) (tn : 0≤T) (a1 : 1≤a)
    (rr : R*q^2≤164*T) (wb : Bw≤4*T) (zb : Bz*q≤10*T) :
    2*Bw*sqrt q*a/q+2*Bz*sqrt q*a+(22/10)*q*R≤430*T*a/sqrt q := by
  have qp : 0<q:=by linarith
  have sq:=Real.sq_sqrt qp.le
  have sp:=Real.sqrt_pos.mpr qp
  have s1 : 1≤sqrt q:=by simpa using Real.sqrt_le_sqrt q1
  have d : 2*Bw*sqrt q*a/q*sqrt q=2*Bw*a:=by
    calc _ = (2*Bw*a)*(sqrt q)^2/q:=by ring
         _ = _:=by rw [sq]; field_simp
  have d2 : 2*Bz*sqrt q*a*sqrt q=2*(Bz*q)*a:=by
    calc _ = 2*(Bz*(sqrt q)^2)*a:=by ring
         _ = _:=by rw [sq]
  have sum1:=mul_le_mul_of_nonneg_right wb (show 0≤a by linarith)
  have sum2:=mul_le_mul_of_nonneg_right zb (show 0≤a by linarith)
  have rem : R*q*sqrt q≤164*T:=by
    by_cases rn : 0≤R
    · have s : sqrt q≤q:=by nlinarith only [sq,mul_nonneg sp.le (sub_nonneg.mpr s1)]
      exact (mul_le_mul_of_nonneg_left s (mul_nonneg rn qp.le)).trans (by nlinarith only [rr])
    · have non:=mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge rn) qp.le) sp.le
      linarith only [non,tn]
  apply (le_div_iff₀ sp).mpr
  rw [add_mul,add_mul,d,d2]
  nlinarith only [sum1,sum2,rem,mul_nonneg tn (sub_nonneg.mpr a1),tn]
end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.presupuesto_de_resto_y_saltos
#print axioms ArticuloA.Historias.presupuesto_de_la_envolvente
