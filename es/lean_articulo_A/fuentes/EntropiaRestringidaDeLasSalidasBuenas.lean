import DeLaCotaDeAbsorcionALaRaiz
open scoped NNReal BigOperators Interval
namespace ArticuloA.Historias
open Filter Set MeasureTheory Perfil Real
noncomputable section
open Trayectoria Trayectoria.E2 Trayectoria.E2.Regular Trayectoria.ProfileKernel RealFinita Corte Repair Limites
open scoped Topology

private theorem entropia_de_una_masa (p a : ℝ) (pn : 0≤p) (ap : 0<a) :
    -(p*log p) ≤ -(p*log a)+a-p := by
  rcases pn.eq_or_lt with eq|pp
  · rw [←eq]; linarith
  have h:=mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos ap pp)) pp.le
  rw [Real.log_div ap.ne' pp.ne'] at h
  have r : p*(a/p-1)=a-p := by field_simp
  rw [r] at h
  linarith

private theorem entropia_sobre_familia {ι : Type*} (s : Finset ι) (p : ι→ℝ) (N : ℝ)
    (pn : ∀ i∈s,0≤p i) (np : 0<N) (cap : (s.card:ℝ)≤N) :
    (∑ i∈s,-(p i*log (p i))) ≤
      (∑ i∈s,p i)*log (2*N)+(1/2:ℝ)-(∑ i∈s,p i) := by
  let a:=(2*N)⁻¹
  have pos : 0<a:=by dsimp [a]; positivity
  have la : log a= -log (2*N):=Real.log_inv _
  have term (i) (hi : i∈s) : -(p i*log (p i))≤p i*log (2*N)+a-p i :=by
    simpa [la] using entropia_de_una_masa (p i) a (pn _ hi) pos
  have h:=Finset.sum_le_sum term
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.sum_mul,Finset.sum_const,nsmul_eq_mul] at h
  have mass : (s.card:ℝ)*a≤1/2:=by
    dsimp [a]
    rw [←div_eq_mul_inv]
    apply (div_le_iff₀ (by positivity : 0<2*N)).mpr
    linarith
  linarith

/-- Entropía de historias, separadas por su salida legal.
Una salida buena admite como máximo q! ordenaciones. -/
theorem entropia_restringida_de_historias {ι : Type*} (b g : Finset ι) (p : ι→ℝ)
    {n q O : ℕ} (np : 0<n) (op : 0<O) (pn : ∀ i,0≤p i)
    (mass : (∑ i∈g,p i)+(∑ i∈b,p i)=1) (gc : g.card≤q.factorial*O)
    (bc : b.card≤n^(2*q)) :
    (∑ i∈g,-(p i*log (p i)))+(∑ i∈b,-(p i*log (p i)))
       -log q.factorial - log 2 - (∑ i∈b,p i)*(2*q*log n) ≤ log O := by
  let G : ℝ:=(q.factorial:ℝ)*O
  let B : ℝ:=(n:ℝ)^(2*q)
  have gp : 0<G:=by dsimp [G]; positivity
  have bp : 0<B:=by dsimp [B]; positivity
  have ge : (1:ℝ)≤G:=by dsimp [G]; exact_mod_cast (show 1≤q.factorial*O from Nat.mul_pos (Nat.factorial_pos _) op)
  have hg:=entropia_sobre_familia g p G (fun i _=>pn i) gp (by dsimp [G]; exact_mod_cast gc)
  have hb:=entropia_sobre_familia b p B (fun i _=>pn i) bp (by dsimp [B]; exact_mod_cast bc)
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) gp.ne'] at hg
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) bp.ne'] at hb
  have nonneg : 0≤∑ i∈b,p i:=Finset.sum_nonneg (fun i _=>pn i)
  have bound:=mul_le_mul_of_nonneg_right (by linarith only [mass,nonneg] : (∑ i∈g,p i)≤1) (Real.log_nonneg ge)
  have total := congrArg (fun t:ℝ=>t*log 2) mass
  have lb : log B=2*q*log n:=by dsimp [B]; rw [Real.log_pow]; push_cast; ring
  have lg : log G=log q.factorial+log O:=Real.log_mul (by positivity) (by positivity)
  rw [lb] at hb
  simp only [mul_add] at hg hb
  simp only [add_mul,one_mul] at total bound
  linarith only [hg,hb,total,mass,bound,lg]

end
end ArticuloA.Historias
#print axioms ArticuloA.Historias.entropia_restringida_de_historias
