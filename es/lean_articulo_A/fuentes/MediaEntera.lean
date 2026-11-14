import Solapamiento
namespace ArticuloA.Trayectoria
open ArticuloA.Corte
variable {α X ι : Type} (s : ProfileScale α)

/-- Unnormalized weighted mean of a natural-valued observable. -/
def meanN (row : Atoms α X) (f : X → Nat) := s.sum row (fun a => s.times (f a.2) a.1)

theorem plus_times (i j : Nat) (v : α) : s.times (i+j) v = s.add (s.times i v) (s.times j v) := by
  induction i with
  | zero => simp [MassScale.times,s.zero_add]
  | succ i ih => rw [Nat.succ_add]; change s.add v _ = s.add (s.add v _) _; rw [ih,s.assoc]

theorem le_times {i j : Nat} (h : i ≤ j) (v : α) : s.le (s.times i v) (s.times j v) := by
  obtain ⟨u,rfl⟩ := Nat.le.dest h
  rw [plus_times]; have b := s.mono (s.refl (s.times i v)) (s.zero_le (s.times u v))
  simpa [s.comm _ s.zero,s.zero_add] using b

theorem mean_le (row : Atoms α X) (f g : X → Nat) (h : ∀ a ∈ row, f a.2 ≤ g a.2) :
    s.le (meanN s row f) (meanN s row g) :=
  s.sum_mono row _ _ (fun a ha => le_times s (h a ha) _)

theorem mean_eq (row : Atoms α X) (f g : X → Nat) (h : ∀ a ∈ row, f a.2 = g a.2) :
    meanN s row f = meanN s row g := by
  induction row with
  | nil => rfl
  | cons a row ih =>
    change s.add (s.times (f a.2) _) (meanN s row f) = s.add (s.times (g a.2) _) (meanN s row g)
    rw [h a (by simp),ih (fun i hi => h i (by simp [hi]))]

theorem mean_plus (row : Atoms α X) (f g : X → Nat) : meanN s row (fun a => f a+g a) =
    s.add (meanN s row f) (meanN s row g) := by
  induction row with
  | nil => exact (s.zero_add _).symm
  | cons a row ih =>
    change s.add (s.times (f a.2+g a.2) a.1) (meanN s row (fun x => f x+g x)) =
      s.add (s.add (s.times (f a.2) a.1) (meanN s row f)) (s.add (s.times (g a.2) a.1) (meanN s row g))
    rw [plus_times,ih,s.assoc,←s.assoc (s.times (g a.2) a.1),s.comm (s.times (g a.2) a.1) _,s.assoc,←s.assoc]

theorem mean_zero (row : Atoms α X) : meanN s row (fun _ => 0) = s.zero := by
  induction row with
  | nil => rfl
  | cons a row ih => change s.add s.zero (meanN s row (fun _ => 0)) = s.zero; rw [ih,s.zero_add]

theorem mean_count (row : Atoms α X) (ks : List ι) (hit : X → ι → Bool) :
    meanN s row (fun a => ks.countP (hit a)) =
    s.sum ks (fun i => meanN s row (fun a => (hit a i).toNat)) := by
  induction ks with
  | nil => exact mean_zero s row
  | cons i ks ih =>
    have eq : (fun a => (i::ks).countP (hit a)) = fun a => (hit a i).toNat+ks.countP (hit a) := by
      funext a; cases h : hit a i <;> simp [List.countP_cons,h,Nat.add_comm]
    rw [eq,mean_plus,ih]; rfl

theorem exchange_bound (row : Atoms α X) (ks : List ι) (hit : X → ι → Prop) (b : α)
    (two : ∀ ij ∈ E2.pairs ks, s.le (meanN s row (fun a =>
      ArticuloA.Repair.indicator (hit a ij.1 ∧ hit a ij.2))) b) :
    s.le (meanN s row (fun a => E2.deathsOn ks (hit a)-1)) (s.times (E2.pairs ks).length b) := by
  classical
  apply s.trans (mean_le s row _ (fun x => E2.doubleOn ks (hit x)) (fun a _ => E2.excess_le_double ks (hit a.2)))
  unfold E2.doubleOn
  rw [mean_count]
  have le := s.sum_mono (E2.pairs ks) (fun ij => meanN s row
    (fun a => (decide (hit a ij.1 ∧ hit a ij.2)).toNat)) (fun _ => b) (by
    intro ij hij
    have eq : (fun a => (decide (hit a ij.1 ∧ hit a ij.2)).toNat) = fun a =>
        ArticuloA.Repair.indicator (hit a ij.1 ∧ hit a ij.2) := by
      funext a; by_cases h : hit a ij.1 ∧ hit a ij.2 <;> simp [ArticuloA.Repair.indicator,h]
    dsimp only; rw [eq]; exact two ij hij)
  have rep (L : List (ι×ι)) : s.sum L (fun _ => b) = s.times L.length b := by
    induction L with
    | nil => rfl
    | cons i L ih => change s.add b (s.sum L _) = s.add b (s.times L.length b); rw [ih]
  rw [rep] at le; exact le
end ArticuloA.Trayectoria
#print axioms ArticuloA.Trayectoria.exchange_bound
