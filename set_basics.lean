-- Kuratowski, Mostowski "Teoria mnogosci":
-- np wprowadza on reguly takie i nazewnictwo jak:
-- ∧ - koniunkcja
-- ∨ - alternatywa
-- ≡ rownowaznosc lub ⟷ (ale caly czas uzywa 1)
-- ⟶ - implikacja
-- ¬ - negacja
-- ≡ mowi, ze mozna okreslac jako p⟶q ∧ q⟶p
-- V - oznacza prawdziwe zdanie, F- zdanie falszywe
-- wprowadza 18 zasad takich jak:
-- (F∧F) ≡ F, itd.
-- pozniej podaje najwazniejsze prawa logiczne wraz z ich nazwami (z 20 lub 30)
-- definiowanych wlasnie przez ≡ pozniej wprowadza podstawowe aksjomaty mnogosci
-- ale chyba tej naiwnej wersji na poczatek nie ZFC.
set_option linter.unusedVariables false
notation "V" => True
notation "F" => False
infix:20 (priority := high) "≡" => Iff
variable {p q r : Prop}(h:p)(hq:q)
def podwojna_negacja (p : Prop) := ¬(¬p) → p
#check False.elim
namespace TautKoniunkcji
theorem FF : F ∧ F ≡ F :=
Iff.intro
  (fun (zal : F ∧ F) =>
    have krok1 : F := zal.left
    krok1)
  (fun (zal : F) =>
    have krok2 : F ∧ F := And.intro zal zal
    krok2)
theorem FV : F∧V ≡ F :=
Iff.intro
  (fun (zal : F∧V) =>
    have k1 : F := zal.left
    k1)
  (fun (zal : F) =>
    have k2 : F∧V := And.intro zal (False.elim zal)
    k2)
theorem VF : V ∧ F ≡ F :=
  Iff.intro
    (fun (zal : V ∧ F) => zal.right)
    (fun (zal : F) => And.intro True.intro zal)
theorem VV : V∧V ≡ V :=
  Iff.intro
    (fun (zal : V∧V) => zal.left)
    (fun (zal : V) => And.intro zal zal)
end TautKoniunkcji
theorem NegF : ¬F ≡ V :=
Iff.intro
  (fun (zal : ¬F) =>
    have k1 : V := True.intro
    k1)
  (fun (zal : V) =>
    have k2 : ¬F := fun (falsz : F) => falsz
    k2)
theorem NegPr : ¬V ≡ F :=
Iff.intro
  (fun (zal : ¬V) =>
    have k1 : F := zal True.intro
    k1)
  (fun (zal : F) =>
    have k2 : ¬V := False.elim zal
    k2)
namespace TautAlt
theorem FF : F∨F ≡ F :=
  Iff.intro
    (fun (zal : F∨F) => Or.elim zal (fun (l : F) => l) (fun (p : F) => p))
    (fun (zal : F) => Or.inl zal)
theorem FV : F∨V ≡ V :=
  Iff.intro
    (fun (zal : F∨V) => Or.elim zal (fun (l : F) => True.intro) (fun (p : V) => p))
    (fun (zal : V) => Or.inr zal)
theorem VF : V∨F ≡ V :=
  Iff.intro
    (fun (zal : V∨F) => Or.elim zal (fun (l : V) => l) (fun (p : F) => True.intro))
    (fun (zal:V) => Or.inl zal)
theorem VV : V∨V ≡ V :=
  Iff.intro
    (fun (zal : V∨V) => Or.elim zal (fun (p :V) =>p) (fun(l:V)=>l))
    (fun(zal:V)=>Or.inl zal)
end TautAlt
namespace TautImpl
theorem FF : F → F ≡ V :=
  Iff.intro
    (fun (zal : F → F) => True.intro)
    (fun (zal : V) =>
      have k1 : F→F := fun (h : F) => h
      k1)
theorem FV : F→V ≡ V :=
  Iff.intro
    (fun (zal:F→V) => True.intro)
    (fun (zal : V) =>
      have k1 : F → V := fun (h : F) => True.intro
      k1)
theorem VF : V→F ≡ F :=
  Iff.intro
    (fun (zal : V→F) => zal True.intro)
    (fun (zal : F) =>
      have k1 : V → F := NegPr.mpr zal
      k1)
theorem VV : V→V ≡ V := imp_self
end TautImpl
namespace TautRown
theorem FF : (F≡F) ≡ V :=
  Iff.intro
    (fun (zal : F≡F) => True.intro)
    (fun (zal : V) =>
      have k1 : F≡F := Iff.intro (fun (f : F) => f) (fun (f : F) => f)
      k1)
theorem FV : (F≡V)≡F :=
  Iff.intro
    (fun (zal : F≡V) => zal.mpr True.intro)
    (fun (zal : F) => Iff.intro
      (fun (f : F) => True.intro)
      (fun (v : V) => zal))
theorem VF : (V≡F)≡F :=
  Iff.intro
    (fun(zal : V≡F) => zal.mp True.intro)
    (fun(zal: F) => Iff.intro
      (fun (v:V)=>zal)
      (fun (f:F)=>True.intro))
theorem VV : (V≡V)≡V :=
  Iff.intro
    (fun (zal:V≡V)=>True.intro)
    (fun (v : V) => Iff.intro
      (fun (v1:V)=>v1)
      (fun (v2:V)=>v2))
end TautRown
namespace PrawaL
theorem PrzemiennoscAlternatywy : (p∨q) ≡ (q∨p) := Or.comm
theorem LacznoscAlternatywy :((p∨q)∨r) ≡ (p∨(q∨r)) := or_assoc
theorem PrzemiennoscKoniunkcji : p∧q ≡ q∧p := and_comm
theorem LaczanoscKoniunkcji : (p∧q)∧r ≡ p∧(q∧r) := and_assoc
theorem PrawRozdzielnosciI : (p∧(q∨r)) ≡ (p∧q)∨(p∧r) :=
  Iff.intro
    (fun (zal : p ∧ (q∨r)) =>
      have k1 : p := zal.left
      have k2 : q∨r := zal.right
    Or.elim k2
      (fun (hq : q) =>
        have hpq : p∧q := And.intro zal.left hq
      Or.inl hpq
      )
      (fun (hr : r) =>
        have hpr : p∧r := And.intro zal.left hr
      Or.inr hpr))
    (fun (zal : (p∧q)∨(p∧r) ) =>
    Or.elim zal
      (fun (h1 : p∧q) =>
        have hp : p := h1.left
        have hqr : q∨r := Or.inl h1.right
      And.intro hp hqr)
      (fun (h2 : p∧r) =>
        have hp : p := h2.left
        have hqr : q∨r := Or.inr h2.right
      And.intro hp hqr)
    )
theorem PrawRozdzielnosciII : (p ∨ (q∧r)) ≡ (p∨q) ∧ (p∨r) := or_and_left
theorem PrawTaut1 : (p∨p) ≡ p :=
Iff.intro
  (fun (hpp: p∨p) => Or.elim hpp (fun(h1:p)=>h1) (fun(h2:p)=>h2))
  (fun (hp : p) => Or.inl hp)
theorem PrawTaut2 : (p∧p) ≡ p := and_self_iff
theorem PrawPochlaniania1 : (p∧F) ≡ F :=
  Iff.intro
    (fun (hpf : p∧F) => hpf.right)
    (fun (h : F) => And.intro (@False.elim p h) h)
theorem PrawPochlaniania2 : (p∧V) ≡ p :=
  Iff.intro
    (fun (h:p∧V) => h.left)
    (fun (h:p) => And.intro h True.intro)
theorem PrawPochlaniania3 : (p∨F) ≡ p :=
  Iff.intro
    (fun(hp : p∨F) => Or.elim hp (fun(h:p)=>h) (fun(hf:F)=> @False.elim p hf))
    (fun(hp:p) => Or.inl hp)
theorem PrawPochlaniania4 : (p∨V) ≡ V :=
  Iff.intro
    (fun(hp:p∨V)=>True.intro)
    (fun(hv : V)=>Or.inr hv)
theorem Sylogizm : (((p → q) ∧ (q → r)) → (p → r)) :=
  fun (h1 : (p→q) ∧ (q→r)) =>
    have k1 : p → q := h1.left
    have k2 : q → r := h1.right
  fun (hp : p) => k2 (k1 hp)
theorem PrawWylaczonegoSrodka : (p ∨ ¬p) ≡ V :=
  Iff.intro
    (fun (h : p∨¬p)=> True.intro)
    (fun (v : V) => Classical.em p)
theorem PrawSprzecznosci : (p ∧ ¬p) ≡ F :=
Iff.intro
  (fun(hp : (p∧¬p)) => hp.right (hp.left))
  (fun (hf : F) => @False.elim (p∧¬p) hf)
theorem PrawPodwojnegoPrzeczenia : p ≡ ¬¬p :=
Iff.intro
  (fun (hp:p)=> fun (hf:¬p)=> hf hp)
  (fun (hnnp : ¬¬p) =>
    Or.elim (Classical.em p)
      (fun (hp : p)=> hp)
      (fun (hnp : ¬p)=> @False.elim p (hnnp hnp)))
theorem PrawMorgana1 : ¬(p∨q) ≡ (¬p∧¬q) :=
  Iff.intro
    (fun (h1 : ¬(p∨q)) =>
      have k1 : ¬p := fun (hp:p) => h1 (Or.inl hp)
      have k2 : ¬q := fun (hq:q) => h1 (Or.inr hq)
    And.intro k1 k2)
    (fun (h2: ¬p∧¬q) => fun (hpq : p ∨ q) =>
    Or.elim hpq (fun (hp:p) => h2.left hp) (fun (hq:q) => h2.right hq))
theorem PrawMorgana2 : ¬(p∧q) ≡ (¬p∨¬q) :=
  Iff.intro
    (fun(hnpq : ¬(p∧q)) =>
      Or.elim (Classical.em p)
        (fun (hp : p) =>
          have hnq : ¬q := fun(hq:q)=> hnpq (And.intro hp hq)
        Or.inr hnq)
        (fun(hq:¬p) => Or.inl hq))
    (fun(hpq : ¬p∨¬q) => fun (hp : p∧q) =>
      have k3 : p := hp.left
      have k4 : q := hp.right
    Or.elim hpq (fun (hnp : ¬p) => hnp k3) (fun(hnq:¬q)=>hnq k4))
theorem PrawKontrapozycji : (p → q) → (¬q → ¬p) :=
  fun (h : p → q) => fun (hnq : ¬q) => fun (hp : p) => hnq (h hp)
theorem Kontr2 : (p → q) ≡ (¬p∨q) :=
  Iff.intro
    (fun (h1 : p → q) =>
    Or.elim (Classical.em p) (fun(hp:p) => Or.inr (h1 hp)) (fun(hnp:¬p) => Or.inl hnp))
    (fun (hpq : ¬p ∨ q) => fun (hp : p) =>
    Or.elim hpq (fun(hnp:¬p) => @False.elim q (hnp hp)) ( fun(hq:q) => hq))
theorem Kontr3 : F → p := fun (hf : F) => @False.elim p hf
theorem Kontr4 : p→p := fun (hp : p) => hp
theorem Kontr5 : p→V := fun (hp : p) => True.intro
theorem WprAltL : p → (p∨q) := fun (hp : p) => Or.inl hp
theorem WprAltP : q → (p ∨q) := fun (hq:q) => Or.inr hq
theorem Przechodniosc : ((p→q)∧(q→r)) → (p→r) :=
  fun (h : (p→q)∧(q→r)) => fun (h2 : p) => h.right (h.left h2)
theorem KnElL : (p∧q) → p := fun(h:p∧q) => h.left
theorem KnElP : (p∧q) → q := fun (h:p∧q) => h.right
end PrawaL
universe u
variable (α : Type u) (p : Prop)(h : p)
def Set (α : Type u) := α → Prop
#check (fun (hp:p)=>fun(hf:¬p)=>hf hp)

-- Teoria mnogosci: Poczatek
axiom Zbior : Type u
axiom nalezy : Zbior.{u} → Zbior.{u} → Prop
infix:50 (priority := high) "∈" => nalezy
notation:50 (priority := high) x "∉" A => ¬(x∈A)

-- Aksjomat jednoznacznosci (ekstensjonalnosc)
axiom eksten (A B : Zbior.{u}) : (∀x:Zbior.{u}, x∈A ≡ x∈B) → A = B

-- Aksjomat sumy
axiom suma (A B : Zbior.{u}) : ∃(C : Zbior.{u}), ∀(x : Zbior.{u}), x∈C ≡ (x∈A ∨ x∈B)

-- Aksjomat Roznicy
axiom roznica (A B : Zbior.{u}) : ∃ (C : Zbior.{u}), ∀(x : Zbior.{u}), x∈C ≡ (x∈A ∧ x∉B)

-- Aksjomat Istnienia
axiom ist : ∃ (A : Zbior.{u}), True

noncomputable def Suma (A B : Zbior.{u}) : Zbior.{u} := Classical.choose (suma A B)
infixl:65 (priority := high) "∪" => Suma

noncomputable def Roznica (A B :Zbior.{u}) : Zbior.{u} := Classical.choose (roznica A B)
infixl:70 (priority := high) "\\" => Roznica

#print Classical.choose
noncomputable def Przekroj (A B : Zbior.{u}) : Zbior.{u} := A\(A\B)
infixl:70 (priority := high) "∩" => Przekroj

noncomputable def Ist : Zbior.{u} := Classical.choose (ist)
#check Ist
noncomputable def Pusty : Zbior.{u} := Ist\Ist
notation:max "Ø" => Pusty

theorem NicNieNalDoPust {x} : x∉Ø :=
fun (hx : x∈Ø) =>
  have krok1 := Classical.choose_spec (roznica Ist Ist) x
  have krok2 : x∈Ist ∧ x∉Ist := krok1.mp hx
krok2.right krok2.left
theorem noww {x} : x∉Ø :=
Classical.byContradiction
(fun (hn:¬(x∉Ø)) =>
  have k : x∈Ø := (@PrawaL.PrawPodwojnegoPrzeczenia (x∈Ø)).mpr hn
  have krok1 := Classical.choose_spec (roznica Ist Ist) x
  have krok2 : x∈Ist ∧ x∉Ist := krok1.mp k
PrawaL.PrawSprzecznosci.mp krok2)
theorem NegRoz {x} (A B : Zbior.{u}) : ¬(x∈(A\B))≡(x∉A)∨x∈B :=
  -- Wyciagamy z aksjomatu definicje roznicy
  have krok1 := Classical.choose_spec (roznica A B) x
  -- Mamy teraz krok1 = x∈C ≡ x∈A ∧ x∉B
  Iff.intro
    (fun (hl : x∉A\B) =>
      have krok2 : ¬(x∈A ∧ x∉B) := fun(h: x∈A∧x∉B) => hl (Iff.mpr krok1 h)
      have krok3 : ¬x∈A ∨ ¬(x∉B) := (@PrawaL.PrawMorgana2 (x∈A) (x∉B)).mp krok2
      Or.elim krok3
        (fun (h1 : x∉A) => Or.inl h1)
        (fun (h2: ¬¬(x∈B)) => Or.inr (PrawaL.PrawPodwojnegoPrzeczenia.mpr h2))
    )
    (fun (h1 :(¬x∈A) ∨ x∈B) =>
      fun (h2 : x∈(A\B)) =>
        have krok4 := Iff.mp krok1 h2
        Or.elim h1
          (fun (h3 : x∉A) => h3 krok4.left)
          (fun (h4 : x∈B) => krok4.right h4))
theorem WPust {x} : x∈Ø ≡ F :=
  Iff.intro
    (fun (h : x∈Ø) => noww h)
    (fun (h1 : F) => h1.elim)

theorem przekroj {x} (A B : Zbior.{u}) : x∈(A∩B) ≡ x∈A ∧ x∈B := by
  dsimp [Przekroj]
  dsimp [Roznica]
  have krok1 := Classical.choose_spec (roznica A (A\B)) x
  rw [krok1]
  rw [NegRoz A B]
  rw [PrawaL.PrawRozdzielnosciI]
  rw [@PrawaL.PrawSprzecznosci (x∈A)]
  rw [PrawaL.PrzemiennoscAlternatywy]
  rw [@PrawaL.PrawPochlaniania3 (x∈A ∧ x∈B)]

theorem summa {x} (A B : Zbior.{u}) : x∈(A∪B) ≡ (x∈A ∨ x∈B) := by
  dsimp [Suma]
  have krok1 := Classical.choose_spec (suma A B) x
  rw [krok1]
theorem rozznica {x} (A B : Zbior.{u}) : x∈(A\B) ≡ (x∈A ∧ x∉B) := by
   dsimp [Roznica]
   have krok1 := Classical.choose_spec (roznica A B) x
   rw [krok1]
noncomputable def RozSym (A B : Zbior.{u}) : Zbior.{u} := ((A\B)∪(B\A))
infixl:70 (priority := high) "∸" => RozSym

noncomputable def podzbior (A B : Zbior.{u}): Prop := ∀ (x : Zbior.{u}), (x∈A) → (x∈B)

infix:30 (priority := high) "⊆" => podzbior

noncomputable def wlaspodzbior (A B : Zbior.{u}) := (A⊆B) ∧ A ≠ B

infix:30 (priority := high) "⊂" => wlaspodzbior

theorem rowprzezpodzb (A B : Zbior.{u}) : (A⊆B) ∧ (B⊆A) → A = B := by
  intro h
  apply eksten
  intro x
  have krok1 : x∈A → x∈B := h.left x
  have krok2 : x∈B → x∈A := h.right x
  exact Iff.intro (krok1) (krok2)

theorem PrzechZb (A B C : Zbior.{u}) : (A⊆B) ∧ (B⊆C) → (A⊆C) := by
  intro h
  intro x
  --intro hxA
  --have krok1 : x∈B := h.left x hxA
  --have krok2 : x∈C := h.right x krok1
  exact PrawaL.Przechodniosc (And.intro (h.left x) (h.right x))
namespace Zakon
theorem OdejmowanieSamejOdSiebie (A : Zbior.{u}) : A\A = Ø := by
  apply eksten
  intro x
  rw [rozznica]
  rw [PrawaL.PrawSprzecznosci]
  rw [←WPust]
theorem I (A : Zbior.{u}) : (A∪A) = A := by
  apply eksten
  intro h
  dsimp [Suma]
  have krok1 := Classical.choose_spec (suma A A)
  rw [krok1]
  rw [PrawaL.PrawTaut1]
theorem II (A : Zbior.{u}) : (A∩A) = A := by
  apply eksten
  intro x
  rw [przekroj]
  rw [PrawaL.PrawTaut2]
theorem PrzemiennoscSumZb (A B : Zbior.{u}) : (A∪B) = (B∪A) := by
  apply eksten
  intro x
  have krok1 := Classical.choose_spec (suma A B) x
  have krok2 := Classical.choose_spec (suma B A) x
  unfold Suma
  rw [krok1]
  rw [krok2]
  exact PrawaL.PrzemiennoscAlternatywy
theorem PrzemiennoscPrzekZb (A B : Zbior.{u}) : (A∩B) = (B∩A) := by
  apply eksten
  intro x
  rw [przekroj]
  rw [przekroj]
  rw [PrawaL.PrzemiennoscKoniunkcji]
theorem LacznoscSumZb (A B C: Zbior.{u}) : ((A∪B)∪C) = (A∪(B∪C)) := by
  apply eksten
  intro x
  rw [summa]
  rw [summa]
  rw [summa]
  rw [summa]
  exact PrawaL.LacznoscAlternatywy
theorem LacznoscPrzekrojuZb (A B C : Zbior.{u}) : (A∩B)∩C = A∩(B∩C) := by
  apply eksten
  intro x
  rw [przekroj]
  rw [przekroj]
  rw [PrawaL.LaczanoscKoniunkcji]
  rw [←przekroj]
  rw [←przekroj]
theorem ZbiorWSumL (A B : Zbior.{u}) : A⊆(A∪B) := by
  intro x
  intro hx
  rw [summa]
  exact @PrawaL.WprAltL (x∈A) (x∈B) hx
theorem ZbiorWSumP (A B : Zbior.{u}) : B⊆(A∪B) := by
  intro x
  intro hB
  rw [summa]
  exact @PrawaL.WprAltP (x∈A) (x∈B) hB
theorem PrzekrojWZbL (A B : Zbior.{u}) : (A∩B)⊆A := by
  intro x
  rw [przekroj]
  intro hP
  exact hP.left
theorem PrzekrojWZbP (A B : Zbior.{u}) : (A∩B)⊆B := by
  intro x
  rw [przekroj]
  intro hB
  exact hB.right
theorem RozWZbL (A B : Zbior.{u}) : (A\B)⊆A := by
  intro x
  rw [rozznica]
  intro hR
  exact hR.left
theorem PodzPrzSum (A B : Zbior.{u}) : (A⊆B) ≡ (A∪B)=B := by
  apply Iff.intro
  · intro h_Podz
    apply eksten
    intro x
    rw [summa]
    apply Iff.intro
    · intro hx
      exact Or.elim hx
        (fun (hA : x∈A) => h_Podz x hA)
        (fun (hB : x∈B) => hB)
    · intro xx
      exact Or.inr xx

  · intro h_sum
    intro x
    intro hA
    have krok1 : x∈A ∨ x∈B := Or.inl hA
    have krok2 : x∈(A∪B) := Iff.mpr (summa A B) krok1
    rw [h_sum] at krok2
    exact krok2
theorem PodzPrzPrzek (A B : Zbior.{u}) : (A⊆B) ≡ (A∩B) = A := by
  apply Iff.intro
  · intro h
    apply eksten
    intro x
    rw [przekroj]
    apply Iff.intro
    · intro hl
      exact hl.left
    · intro hA
      have krok1 : x∈B := h x hA
      exact And.intro hA krok1

  · intro hL
    intro x
    intro hA
    have krok1 : x∈A := hA
    rw [← hL] at krok1
    have krok2 : x∈A ∧ x∈B := Iff.mp (przekroj A B) krok1
    exact krok2.right
theorem ZiorPustPodzZb (A : Zbior.{u}) : Ø⊆A := by
  dsimp [podzbior]
  intro x
  intro hO
  exact (NicNieNalDoPust hO).elim
theorem SumaZPust (A : Zbior.{u}) : (A∪Ø) = A := by
  apply eksten
  intro x
  rw [summa]
  rw [WPust]
  rw [PrawaL.PrawPochlaniania3]
theorem PrzZPust (A : Zbior.{u}) : (A∩Ø) = Ø := by
  apply eksten
  intro x
  rw [przekroj]
  rw [WPust]
  rw [PrawaL.PrawPochlaniania1]
theorem PustMZb (A : Zbior.{u}) : (Ø\A) = Ø := by
  apply eksten
  intro x
  rw [rozznica]
  rw [WPust]
  rw [PrawaL.PrzemiennoscKoniunkcji]
  rw [PrawaL.PrawPochlaniania1]
theorem ZbMPust (A : Zbior.{u}) : (A\Ø) = A := by
  apply eksten
  intro x
  rw [rozznica]
  rw [WPust]
  rw [NegF]
  rw [PrawaL.PrawPochlaniania2]
theorem RozlWzgRoz (A B :Zbior.{u}) : ((B\A)=Ø) → (B⊆A) := by
  intro hL
  intro x
  intro hB
  apply Classical.byContradiction
  intro hnA
  have krok1 : x∈B ∧ x∉A:= And.intro hB hnA
  have krok2 : x∈(B\A) := Iff.mpr (rozznica B A) krok1
  rw [hL] at krok2
  exact NicNieNalDoPust krok2
theorem PodzbOdNadzbioru (A B : Zbior.{u}) : A⊆B → A\B = Ø := by
  rw [podzbior]
  intro hAB
  apply eksten
  intro x
  rw [rozznica]
  constructor
  · intro hA_od_B
    rw [WPust]
    have krok1 : x∈B := hAB x hA_od_B.left
    have krok2 : x∈B ∧ ¬x∈B := And.intro krok1 hA_od_B.right
    have krok3 : F := (@PrawaL.PrawSprzecznosci (x∈B)).mp krok2
    exact krok3
  · rw [WPust]
    intro hF
    exact False.elim hF
end Zakon
theorem PrawRozdzielnosciZbI (A B C : Zbior.{u}) : A∩(B∪C) = (A∩B)∪(A∩C) := by
  apply eksten
  intro x
  rw [przekroj]
  rw [summa]
  rw [PrawaL.PrawRozdzielnosciI]
  rw [summa]
  rw [przekroj]
  rw [przekroj]
theorem PrawRozdzielnosciZbII (A B C : Zbior.{u}) : A∪(B∩C) = (A∪B)∩(A∪C) := by
  apply eksten
  intro x
  rw [summa]
  rw [przekroj]
  rw [PrawaL.PrawRozdzielnosciII]
  rw [przekroj]
  rw [summa]
  rw [summa]
theorem PrawOdejmowaniaZbI (A B : Zbior.{u}) : A∪(B\A) = A∪B := by
  apply eksten
  intro x
  rw [summa]
  rw [rozznica]
  rw [PrawaL.PrawRozdzielnosciII]
  rw [PrawaL.PrawWylaczonegoSrodka]
  rw [PrawaL.PrawPochlaniania2]
  rw [summa]
theorem PrawOdejmowaniaZbII (A B : Zbior.{u}) : A⊆B → (A∪(B\A)=B) := by
  intro hA_in_B
  apply eksten
  intro x
  rw [summa]
  rw [rozznica]
  rw [PrawaL.PrawRozdzielnosciII]
  rw [PrawaL.PrawWylaczonegoSrodka]
  rw [PrawaL.PrawPochlaniania2]
  rw [←summa]
  have krok1 : A∪B=B := (Zakon.PodzPrzSum A B).mp hA_in_B
  rw [krok1]
theorem PrawOdejmowaniaZbIII (A B : Zbior.{u}) : A\B = A\(A∩B) := by
  apply eksten
  intro x
  rw [rozznica]
  rw [rozznica]
  rw [przekroj]
  rw [PrawaL.PrawMorgana2]
  rw [PrawaL.PrawRozdzielnosciI]
  rw [PrawaL.PrawSprzecznosci]
  rw [PrawaL.PrzemiennoscAlternatywy]
  rw [PrawaL.PrawPochlaniania3]
theorem PrawRozdzielnosciPrzekrojuWzglOdejm (A B C : Zbior.{u}) : A∩(B\C) = (A∩B)\C := by
  apply eksten
  intro x
  rw [przekroj]
  rw [rozznica]
  rw [rozznica]
  rw [przekroj]
  rw [←PrawaL.LaczanoscKoniunkcji]
theorem PrawMorganaZbI (A B C : Zbior.{u}) : A\(B∩C) = (A\B)∪(A\C) := by
  apply eksten
  intro x
  rw [rozznica]
  rw [przekroj]
  rw [PrawaL.PrawMorgana2]
  rw [PrawaL.PrawRozdzielnosciI]
  rw [summa]
  rw [rozznica]
  rw [rozznica]
theorem PrawMorganaZbII (A B C : Zbior.{u}) : A\(B∪C) = (A\B)∩(A\C) := by
  apply eksten
  intro x
  rw [rozznica]
  rw [summa]
  rw [PrawaL.PrawMorgana1]
  rw [przekroj]
  rw [rozznica]
  rw [rozznica]
  rw [PrawaL.LaczanoscKoniunkcji]
  rw (config := {occs := .pos [4]}) [PrawaL.PrzemiennoscKoniunkcji]
  rw [PrawaL.LaczanoscKoniunkcji]
  rw (config := {occs := .pos [2]}) [←PrawaL.LaczanoscKoniunkcji]
  rw [PrawaL.PrawTaut2]
  rw (config := {occs := .pos [4]}) [PrawaL.PrzemiennoscKoniunkcji]
theorem SumaOdjJedenZb (A B C : Zbior.{u}) : (A∪B)\C = (A\C)∪(B\C) := by
  apply eksten
  intro x
  rw [rozznica]
  rw [summa]
  rw [PrawaL.PrzemiennoscKoniunkcji]
  rw [PrawaL.PrawRozdzielnosciI]
  rw [PrawaL.PrzemiennoscKoniunkcji]
  rw (config := {occs := .pos [2]}) [PrawaL.PrzemiennoscKoniunkcji]
  conv =>
    lhs
    arg 1
    rw [←rozznica]
  conv =>
    lhs
    arg 2
    rw [←rozznica]
  rw [←summa]
theorem OdejmowanieOdRoznic (A B C : Zbior.{u}) : A\(B\C) = (A\B)∪(A∩C) := by
  apply eksten
  intro x
  conv =>
    lhs
    rw [rozznica]
    arg 2
    rw [rozznica]
    rw [PrawaL.PrawMorgana2]
    rw [←PrawaL.PrawPodwojnegoPrzeczenia]
  conv =>
    lhs
    rw [PrawaL.PrawRozdzielnosciI]
    arg 1
    rw [←rozznica]
  rw (config := {occs := .pos [1]}) [←przekroj]
  rw [summa]
theorem OdejmowanieSumy (A B C : Zbior.{u}) : A\(B∪C) = (A\B)\C := by
  apply eksten
  intro x
  conv =>
    rhs
    rw [rozznica]
    rw [rozznica]
    rw [PrawaL.LaczanoscKoniunkcji]
    arg 2
    rw [←PrawaL.PrawMorgana1]
    rw [←summa]
  rw [←rozznica]
theorem StosunekInkluzjiI (A B C D : Zbior.{u}) : ((A⊆B) ∧ (C⊆D)) → (A∪C ⊆ B∪D) := by
    intro h1
    intro x
    intro hAC
    rw [summa] at hAC
    rw [summa]
    cases hAC with
    | inl hA =>
      have krok1 : x∈B := h1.left x hA
      exact Or.inl krok1
    | inr hC =>
      have krok2 : x∈D := h1.right x hC
      exact Or.inr krok2
theorem StosunekInkluzjiII (A B C D : Zbior.{u}) : ((A⊆B)∧(C⊆D)) → (A∩C⊆B∩D) := by
  intro h1
  intro x
  intro hAC
  rw [przekroj] at hAC
  have krok1 : x∈B ∧ x∈D :=  (And.intro (h1.left x hAC.left) (h1.right x hAC.right))
  rw [←przekroj] at krok1
  exact krok1
theorem StosunekInkluzjiIII (A B C D : Zbior.{u}) : (A⊆B)∧(C⊆D) → (A\D⊆B\C) := by
  intro h1
  intro x
  intro hAD
  rw [rozznica] at hAD
  have krok1 : x∈B ∧ ¬x∈C := And.intro (h1.left x hAD.left)
    (PrawaL.PrawKontrapozycji (h1.right x) hAD.right)
  rw [←rozznica] at krok1
  exact krok1
theorem ZbSwoimPodzbiorem (A : Zbior.{u}): A⊆A := by
  intro x
  intro hA
  exact hA
theorem StosunekInkluzjiIV (A C D : Zbior.{u}) : (C⊆D) → (A\D⊆A\C) := by
  intro h1
  have krok1 : A⊆A := ZbSwoimPodzbiorem A
  exact StosunekInkluzjiIII A A C D (And.intro krok1 h1)
theorem RozSymPrzemiennosc (A B : Zbior.{u}) : A∸B = B∸A := by
  apply eksten
  intro x
  conv =>
    lhs
    rw [RozSym]
    rw [summa]
    rw [PrawaL.PrzemiennoscAlternatywy]
    rw [←summa]
    rw [←RozSym]
theorem RozSymLacznoscI (A B C: Zbior.{u}) : A∸(B∸C) = (A\(B∪C))∪(B\(A∪C))∪(C\(A∪B))∪A∩B∩C := by
  apply eksten
  intro x
  conv =>
    lhs
    conv =>
      rhs
      arg 2
      rw [RozSym]
    rw [RozSym]
    rw [summa]
    conv =>
      lhs
      rw [rozznica]
      rw [summa]
      rw [PrawaL.PrawMorgana1]
      rw [rozznica]
      rw [rozznica]
      rw [PrawaL.PrawMorgana2]
      rw [PrawaL.PrawMorgana2]
      rw [←PrawaL.LaczanoscKoniunkcji]
      conv =>
        arg 1
        rw [PrawaL.PrawRozdzielnosciI]
        rw [←rozznica]
        rw [←PrawaL.PrawPodwojnegoPrzeczenia]
      arg 2
      rw [←PrawaL.PrawPodwojnegoPrzeczenia]
    conv =>
      arg 1
      conv =>
        arg 1
        rw [←przekroj]
        rw [←summa]
    conv =>
      arg 2
      rw [rozznica]
      conv =>
        arg 1
        rw [summa]
        rw [rozznica]
        rw [PrawaL.PrzemiennoscAlternatywy]
        rw [PrawaL.PrawRozdzielnosciII]
        rw [rozznica]
        conv =>
          arg 1
          rw [PrawaL.PrzemiennoscAlternatywy]
          rw [PrawaL.PrawRozdzielnosciII]
          rw [PrawaL.PrawWylaczonegoSrodka]
          rw [PrawaL.PrawPochlaniania2]
        arg 2
        rw [PrawaL.PrzemiennoscAlternatywy]
        rw [PrawaL.PrawRozdzielnosciII]
        rw [PrawaL.PrzemiennoscAlternatywy]
        rw [PrawaL.PrawWylaczonegoSrodka]
        rw [PrawaL.PrzemiennoscKoniunkcji]
        rw [PrawaL.PrawPochlaniania2]
        rw [←PrawaL.PrawMorgana2]
    conv =>
      arg 1
      rw [PrawaL.PrawRozdzielnosciI]
      conv =>
        arg 1
        rw [PrawaL.PrzemiennoscKoniunkcji]
        rw [summa]
        rw [PrawaL.PrawRozdzielnosciI]
        conv =>
          arg 2
          rw [przekroj]
          rw [PrawaL.PrzemiennoscKoniunkcji]
          rw [PrawaL.LaczanoscKoniunkcji]
          rw [PrawaL.PrawSprzecznosci]
          rw [PrawaL.PrawPochlaniania1]
        rw [PrawaL.PrawPochlaniania3]
        rw [rozznica]
      conv =>
        arg 2
        rw [summa]
        rw [PrawaL.PrzemiennoscKoniunkcji]
        rw [PrawaL.PrawRozdzielnosciI]
        conv =>
          arg 1
          rw [rozznica]
          rw [PrawaL.PrzemiennoscKoniunkcji]
          rw [PrawaL.LaczanoscKoniunkcji]
          conv =>
            arg 2
            rw [PrawaL.PrzemiennoscKoniunkcji]
            rw [PrawaL.PrawSprzecznosci]
          rw [PrawaL.PrawPochlaniania1]
        rw [PrawaL.PrzemiennoscAlternatywy]
        rw [PrawaL.PrawPochlaniania3]
        rw [przekroj]
      conv =>
        arg 1
        rw [←rozznica]
        rw [PrawaL.PrzemiennoscKoniunkcji]
      conv =>
        arg 2
        rw [←przekroj]
        rw [←przekroj]
    conv =>
      arg 2
      rw [PrawaL.LaczanoscKoniunkcji]
      rw [PrawaL.PrzemiennoscKoniunkcji]
      rw [PrawaL.LaczanoscKoniunkcji]
      conv =>
        arg 2
        rw [PrawaL.PrawRozdzielnosciI]
        conv =>
          arg 1
          rw [PrawaL.PrzemiennoscKoniunkcji]
          rw [←rozznica]
    conv =>
      arg 2
      conv =>
        arg 2
        rw [PrawaL.PrzemiennoscKoniunkcji]
        rw [←rozznica]
        rw [←summa]
        rw [←SumaOdjJedenZb]
    rw [←przekroj]
    conv =>
      arg 2
      rw [PrawaL.PrzemiennoscKoniunkcji]
      rw [←rozznica]
    rw [PrawaL.PrzemiennoscAlternatywy]
    rw [←rozznica]
    conv =>
      arg 2
      conv =>
        arg 2
        rw [przekroj]
        rw [PrawaL.PrzemiennoscKoniunkcji]
        rw [przekroj]
        rw [PrawaL.LaczanoscKoniunkcji]
        conv =>
          arg 2
          rw [PrawaL.PrzemiennoscKoniunkcji]
          rw [←przekroj]
        rw [←przekroj]
    conv =>
      arg 1
      rw [rozznica]
      rw [rozznica]
      conv =>
        arg 1
        rw [PrawaL.PrzemiennoscKoniunkcji]
        rw [summa]
        rw [PrawaL.PrawRozdzielnosciI]
      rw [PrawaL.PrzemiennoscKoniunkcji]
      rw [PrawaL.PrawRozdzielnosciI]
      conv =>
        arg 1
        rw [przekroj]
        conv =>
          arg 2
          rw [PrawaL.PrzemiennoscKoniunkcji]
          rw [←rozznica]
        rw [PrawaL.PrzemiennoscKoniunkcji]
        rw [PrawaL.PrawMorgana2]
        rw [PrawaL.PrawRozdzielnosciI]
        conv =>
          arg 2
          rw [rozznica]
          rw [PrawaL.PrzemiennoscKoniunkcji]
          rw [←PrawaL.LaczanoscKoniunkcji]
          conv =>
            arg 1
            rw [PrawaL.PrzemiennoscKoniunkcji]
            rw [PrawaL.PrawSprzecznosci]
          rw [PrawaL.PrzemiennoscKoniunkcji]
          rw [PrawaL.PrawPochlaniania1]
        rw [PrawaL.PrawPochlaniania3]
        rw [←rozznica]
      conv =>
        arg 2
        rw [przekroj]
        rw [PrawaL.PrawMorgana2]
        conv =>
          arg 2
          rw [PrawaL.PrzemiennoscKoniunkcji]
          rw [←rozznica]
        rw [PrawaL.PrzemiennoscKoniunkcji]
        rw [PrawaL.PrawRozdzielnosciI]
        conv =>
          arg 1
          rw [rozznica]
          rw [PrawaL.PrzemiennoscKoniunkcji]
          rw [←PrawaL.LaczanoscKoniunkcji]
          conv =>
            arg 1
            rw [PrawaL.PrzemiennoscKoniunkcji]
            rw [PrawaL.PrawSprzecznosci]
          rw [PrawaL.PrzemiennoscKoniunkcji]
          rw [PrawaL.PrawPochlaniania1]
        rw [PrawaL.PrzemiennoscAlternatywy]
        rw [PrawaL.PrawPochlaniania3]
        rw [rozznica]
        rw [PrawaL.LaczanoscKoniunkcji]
        rw [←PrawaL.PrawMorgana1]
        rw [←summa]
        rw [←rozznica]
      conv =>
        arg 1
        rw [rozznica]
        rw [rozznica]
        rw [PrawaL.LaczanoscKoniunkcji]
        rw [←PrawaL.PrawMorgana1]
        rw [←summa]
        rw [←rozznica]
    conv =>
      arg 2
      conv =>
        arg 1
        rw [rozznica]
        rw [rozznica]
        rw [PrawaL.LaczanoscKoniunkcji]
        rw [←PrawaL.PrawMorgana1]
        rw [←summa]
        rw [←rozznica]
    rw [PrawaL.PrzemiennoscAlternatywy]
    rw [PrawaL.LacznoscAlternatywy]
    conv =>
      arg 2
      rw [PrawaL.PrzemiennoscAlternatywy]
    rw [←summa]
    rw [←summa]
    rw [←summa]
    conv =>
      arg 2
      conv =>
        arg 2
        conv =>
         arg 2
         rw [←Zakon.LacznoscPrzekrojuZb]
      rw [←Zakon.LacznoscSumZb]
      rw [←Zakon.LacznoscSumZb]
theorem SymRozdoS (A B C : Zbior.{u}) : (A∸B)∸C = (A\(B∪C))∪(B\(A∪C))∪(C\(A∪B))∪A∩B∩C := by
  apply eksten
  intro x
  have krok1 : B∩C⊆C := @Zakon.PrzekrojWZbP B C
  have krok2 : B∩C∪C = C := (@Zakon.PodzPrzSum (B∩C) C).mp krok1
  have krok3 : C⊆C∪B := @Zakon.ZbiorWSumL C B
  have krok4 : C∩(C∪B) = C := (@Zakon.PodzPrzPrzek C (C∪B)).mp krok3
  have krok6 : C∩B⊆C := @Zakon.PrzekrojWZbL C B
  have krok5 : (C∩B)⊆(C∪B) := PrzechZb (C∩B) C (C∪B) (And.intro krok6 krok3)
  have krok7 : (C∩B)∩(C∪B) = (C∩B) := (@Zakon.PodzPrzPrzek (C∩B) (C∪B)).mp krok5
  have krok8 : B∩(C\A)⊆C\A := @Zakon.PrzekrojWZbP B (C\A)
  have krok9 : B∩(C\A)∪(C\A) = C\A := (@Zakon.PodzPrzSum (B∩(C\A)) (C\A)).mp krok8
  have krok10 : B∩C⊆B∩C∪(C\(A∩B)) := Zakon.ZbiorWSumL (B∩C) (C\(A∩B))
  have krok11 : (B∩C)∩(B∩C∪(C\(A∩B))) = B∩C := (Zakon.PodzPrzPrzek (B∩C) (B∩C∪(C\(A∩B)))).mp krok10
  have krok12 :  A\B⊆A := Zakon.RozWZbL A B
  have krok13 : A⊆A∪B∩C := Zakon.ZbiorWSumL A (B∩C)
  have krok14 :  A∩(B∩C)⊆B∩C := @Zakon.PrzekrojWZbP A (B∩C)
  have krok15 : A⊆A := ZbSwoimPodzbiorem A
  have krok16 : A∩(B∩C) ⊆ B∩C := Zakon.PrzekrojWZbP A (B∩C)
  have krok17 : (A∩(B∩C)∪A)⊆(B∩C∪A) := StosunekInkluzjiI (A∩(B∩C)) (B∩C) A A (And.intro krok16 krok15)
  have krok18 : A∩C⊆C := Zakon.PrzekrojWZbP A C
  have krok19 : A\B⊆A\B := ZbSwoimPodzbiorem (A\B)
  have krok20 : A∩C\(A\B)⊆C\(A\B) := StosunekInkluzjiIII (A∩C) (C) (A\B) (A\B) (And.intro krok18 krok19)
  have krok21 : ((A∩(B∩C))⊆B∩C) ∧ (B∩C⊆(C\A∪(B∩C))) := And.intro
    (Zakon.PrzekrojWZbP A (B∩C))
    (Zakon.ZbiorWSumP (C\A) (B∩C))
  have krok22 : (A∩(B∩C))⊆(C\A∪(B∩C)) := (PrzechZb (A∩(B∩C)) (B∩C) (C\A∪(B∩C))) krok21
  conv =>
    lhs
    rw [RozSym]
    conv =>
      rhs
      conv =>
        lhs
        rw [RozSym]
        rw [SumaOdjJedenZb]
  rw [summa]
  rw [summa]
  rw [rozznica]
  rw [rozznica]
  conv =>
    arg 1
    conv =>
      arg 1
      conv =>
        arg 1
        rw [PrawaL.LaczanoscKoniunkcji]
        rw [←PrawaL.PrawMorgana1]
        rw [←summa]
        rw [←rozznica]
      conv =>
        arg 2
        rw [rozznica]
        rw [rozznica]
        rw [PrawaL.LaczanoscKoniunkcji]
        rw [←PrawaL.PrawMorgana1]
        rw [←summa]
        rw [←rozznica]
      rw [←summa]
    conv =>
      arg 2
      rw [rozznica]
      rw [RozSym]
      rw [summa]
      rw [PrawaL.PrawMorgana1]
      conv =>
        arg 2
        rw [rozznica]
        rw [rozznica]
        rw [PrawaL.PrawMorgana2]
        rw [PrawaL.PrawMorgana2]
        rw [←PrawaL.PrawPodwojnegoPrzeczenia]
        rw [←PrawaL.PrawPodwojnegoPrzeczenia]
      rw [←PrawaL.LaczanoscKoniunkcji]
      conv =>
        arg 1
        rw [PrawaL.PrawRozdzielnosciI]
        conv =>
          arg 2
          rw [PrawaL.PrzemiennoscKoniunkcji]
          rw [←przekroj]
        rw [←rozznica]
        rw [←summa]
      rw [PrawaL.PrawRozdzielnosciI]
      conv =>
        arg 1
        rw [PrawaL.PrzemiennoscKoniunkcji]
        rw [summa]
        rw [PrawaL.PrawRozdzielnosciI]
        conv =>
          arg 1
          rw [PrawaL.PrzemiennoscKoniunkcji]
          rw [rozznica]
          rw [PrawaL.LaczanoscKoniunkcji]
          rw [←PrawaL.PrawMorgana1]
          rw [←summa]
          rw [←rozznica]
        conv =>
          arg 2
          rw [PrawaL.PrzemiennoscKoniunkcji]
          rw [←rozznica]
      rw [PrawaL.LacznoscAlternatywy]
      conv =>
        arg 2
        rw [PrawaL.PrawRozdzielnosciII]
        conv =>
          arg 1
          rw [PrawaL.PrzemiennoscAlternatywy]
          rw [summa]
          rw [PrawaL.LacznoscAlternatywy]
          conv =>
            arg 2
            rw [rozznica]
            rw [PrawaL.PrawRozdzielnosciII]
            rw [PrawaL.PrawTaut1]
        conv =>
          arg 2
          rw [PrawaL.PrzemiennoscAlternatywy]
          rw [rozznica]
          rw [PrawaL.PrawRozdzielnosciII]
          conv =>
            arg 2
            conv =>
            arg 1
            rw [@PrawaL.PrawPodwojnegoPrzeczenia (x∈A)]
          conv =>
            arg 2
            rw [←PrawaL.PrawMorgana2]
            rw [PrawaL.PrzemiennoscKoniunkcji]
            rw [←rozznica]
          rw [PrawaL.PrzemiennoscKoniunkcji]
          rw [PrawaL.PrawRozdzielnosciI]
          conv =>
            arg 1
            rw [rozznica]
            rw [PrawaL.PrawMorgana2]
            rw [PrawaL.PrzemiennoscKoniunkcji]
            rw [PrawaL.PrawRozdzielnosciI]
            rw [←PrawaL.PrawPodwojnegoPrzeczenia]
            rw [PrawaL.PrawTaut2]
            rw [←rozznica]
        conv =>
          arg 1
          conv =>
            arg 2
            rw [PrawaL.PrawRozdzielnosciI]
            rw [PrawaL.PrawTaut2]
            rw [←rozznica]
            rw [PrawaL.PrzemiennoscAlternatywy]
          rw [←PrawaL.LacznoscAlternatywy]
          conv =>
            arg 1
            conv =>
              arg 2
              rw [rozznica]
            rw [PrawaL.PrawRozdzielnosciII]
        conv =>
          arg 1
          conv =>
            arg 1
            conv =>
              arg 1
              rw [PrawaL.PrzemiennoscAlternatywy]
              rw [rozznica]
              rw [PrawaL.PrawRozdzielnosciII]
              conv =>
                arg 1
                rw [←summa]
              rw [PrawaL.PrawRozdzielnosciI]
              conv =>
                arg 1
                conv =>
                  arg 1
                  rw [summa]
                  rw [PrawaL.PrzemiennoscAlternatywy]
                  rw [←summa]
                  rhs
                  rw [PrawRozdzielnosciZbII]
                  conv =>
                    arg 2
                    rw [Zakon.I]
                conv =>
                  arg 1
                  rw [przekroj]
                rw [PrawaL.LaczanoscKoniunkcji]
                conv =>
                  arg 2
                  rw [przekroj]
                  rw [PrawaL.PrzemiennoscKoniunkcji]
                  rw [PrawaL.LaczanoscKoniunkcji]
                  rw [PrawaL.PrawTaut2]
                  rw [PrawaL.PrzemiennoscKoniunkcji]
                  rw [←przekroj]
              rw [←przekroj]
              rw [PrawaL.PrawRozdzielnosciII]
              conv =>
                arg 1
                rw [PrawaL.PrzemiennoscAlternatywy]
                conv =>
                  arg 2
                  rw [przekroj]
                rw [PrawaL.PrawRozdzielnosciII]
                conv =>
                  arg 1
                  conv =>
                    arg 1
                    rw [krok2]
                  rw [summa]
                  rw [←PrawaL.LacznoscAlternatywy]
                  rw [PrawaL.PrawTaut1]
                  rw [←summa]
                conv =>
                  arg 2
                  rw [krok2]
                  rw [PrawaL.PrzemiennoscAlternatywy]
                  conv =>
                    arg 1
                    rw [przekroj]
                    rw [PrawaL.PrzemiennoscKoniunkcji]
                    rw [←przekroj]
                  rw [←summa]
                  rw [krok2]
                rw [PrawaL.PrzemiennoscKoniunkcji]
                rw [←przekroj]
                rw [krok4]
              conv =>
                arg 2
                conv =>
                  arg 1
                  rw [przekroj]
                  rw [PrawaL.PrzemiennoscKoniunkcji]
                  rw [←przekroj]
                  rw [krok7]
            conv =>
              arg 1
              conv =>
                arg 2
                rw [PrawaL.PrzemiennoscAlternatywy]
                rw [przekroj]
                rw [PrawaL.PrawRozdzielnosciII]
                conv =>
                  arg 1
                  rw [@PrawaL.PrawPodwojnegoPrzeczenia (x∈C)]
                  rw [←PrawaL.PrawMorgana2]
                  rw [←rozznica]
                rw [@PrawaL.PrawPodwojnegoPrzeczenia (x∈B)]
                rw [←PrawaL.PrawMorgana2]
                rw [←rozznica]
                rw [←PrawaL.PrawMorgana1]
                rw [PrawaL.PrzemiennoscAlternatywy]
                rw [←summa]
            rw [←PrawMorganaZbI]
            conv =>
              arg 2
              rw [@PrawaL.PrawPodwojnegoPrzeczenia (x∈C\A)]
              rw [PrawaL.PrzemiennoscAlternatywy]
              rw [←PrawaL.PrawMorgana2]
              rw [←rozznica]
            conv =>
              arg 1
              rw [PrawaL.PrzemiennoscKoniunkcji]
          conv =>
            arg 1
            rw [PrawaL.LaczanoscKoniunkcji]
            conv =>
              arg 2
              conv =>
                arg 2
                rw [rozznica]
                rw [rozznica]
                rw [PrawaL.PrawMorgana2]
                rw [PrawaL.PrzemiennoscAlternatywy]
                rw [←PrawaL.PrawPodwojnegoPrzeczenia]
              rw [PrawaL.PrawRozdzielnosciI]
              conv =>
                arg 1
                rw [←PrawaL.LaczanoscKoniunkcji]
                rw [PrawaL.PrawTaut2]
              rw [←rozznica]
              rw [←rozznica]
              rw [←summa]
              rw [←PrawMorganaZbI]
          rw [PrawaL.PrzemiennoscAlternatywy]
          rw [PrawaL.PrawRozdzielnosciII]
          conv =>
            arg 1
            rw [rozznica]
            rw [PrawaL.PrawMorgana2]
            rw [PrawaL.PrzemiennoscAlternatywy]
            rw [PrawaL.LacznoscAlternatywy]
            rw [←PrawaL.PrawPodwojnegoPrzeczenia]
            rw [PrawaL.PrawTaut1]
          conv =>
            arg 2
            rw [rozznica]
            rw [PrawaL.PrawRozdzielnosciII]
            conv =>
              arg 1
              rw [←summa]
              rw [krok2]
          rw [PrawaL.PrawRozdzielnosciI]
          conv =>
            arg 2
            conv =>
              arg 1
              rw [PrawaL.PrzemiennoscKoniunkcji]
              rw [przekroj]
              rw [PrawaL.LaczanoscKoniunkcji]
              rw [PrawaL.PrawTaut2]
            rw [←rozznica]
            rw [←przekroj]
            rw [←summa]
          rw [PrawaL.PrzemiennoscKoniunkcji]
          rw [PrawaL.PrawRozdzielnosciI]
          conv =>
            arg 1
            rw [PrawaL.PrzemiennoscKoniunkcji]
            rw [summa]
            rw [PrawaL.PrawRozdzielnosciI]
            conv =>
              arg 1
              rw [PrawaL.PrzemiennoscKoniunkcji]
              rw [←rozznica]
            arg 2
            rw [PrawaL.PrzemiennoscKoniunkcji]
            rw [←rozznica]
        conv =>
          arg 1
          conv =>
            arg 1
            rhs
            rw [rozznica]
            rw [rozznica]
            rw [PrawaL.LaczanoscKoniunkcji]
            rw [←PrawaL.PrawMorgana1]
            rw [←summa]
            rw [(@Zakon.PodzPrzSum (A∩B) A).mp (Zakon.PrzekrojWZbL A B)]
            rw [←rozznica]
          rw [←(@PrawRozdzielnosciPrzekrojuWzglOdejm B C A)]
          conv =>
            arg 1
            rw [←summa]
            rw [krok9]
          conv =>
            arg 2
            rw [PrawaL.PrzemiennoscKoniunkcji]
            rw [←przekroj]
            rw [krok11]
        arg 2
        conv =>
          arg 1
          rw [←summa]
          rw [((@Zakon.PodzPrzSum (A\B) A).mp krok12)]
      conv =>
        arg 2
        rhs
        rw [PrawaL.PrawRozdzielnosciII]
        conv =>
          arg 1
          rw [rozznica]
          rw [PrawaL.PrawMorgana2]
          rw [←PrawaL.PrawPodwojnegoPrzeczenia]
          rw [PrawaL.PrzemiennoscAlternatywy]
          rw [PrawaL.LacznoscAlternatywy]
          rw [PrawaL.PrawTaut1]
        rw [←summa]
        rw [PrawaL.PrzemiennoscKoniunkcji]
        rw [PrawaL.PrawRozdzielnosciI]
        conv =>
          arg 2
          rw [PrawaL.PrzemiennoscKoniunkcji]
          rw [←przekroj]
          rw [((Zakon.PodzPrzPrzek A (A∪B∩C)).mp krok13)]
        rw [PrawaL.PrzemiennoscAlternatywy]
        rw [PrawaL.PrawRozdzielnosciII]
        conv =>
          arg 1
          rw [←summa]
          rw [(Zakon.PodzPrzSum A (A∪B∩C)).mp krok13]
        rw [PrawaL.PrawRozdzielnosciI]
        conv =>
          arg 1
          rw [summa]
          rw [PrawaL.PrzemiennoscKoniunkcji]
          rw [PrawaL.PrawRozdzielnosciI]
          rw [PrawaL.PrawTaut2]
          rhs
          rw [przekroj]
          rw [←PrawaL.LaczanoscKoniunkcji]
          rw [←przekroj]
          rw [←przekroj]
        rw [←summa]
        rw [PrawaL.PrawRozdzielnosciII]
        conv =>
          arg 1
          rw [summa]
          rw [PrawaL.PrzemiennoscAlternatywy]
          rw [summa]
          conv =>
            arg 1
            rw [PrawaL.PrzemiennoscAlternatywy]
          rw [PrawaL.LacznoscAlternatywy]
          conv =>
            arg 2
            rw [←PrawaL.LacznoscAlternatywy]
            rw [PrawaL.PrawTaut1]
          rw [PrawaL.PrzemiennoscAlternatywy]
          rw [PrawaL.LacznoscAlternatywy]
          arg 2
          rw [Zakon.LacznoscPrzekrojuZb]
          rw [←summa]
          rw [(Zakon.PodzPrzSum (A∩(B∩C)) (B∩C)).mp krok14]
        rw [←summa]
        rw [PrawaL.PrawRozdzielnosciI]
      rhs
      conv =>
        arg 1
        rw [Zakon.PrzemiennoscPrzekZb]
        rw [←summa]
        rw [←(OdejmowanieOdRoznic C A B)]
      rw [←rozznica]
      conv =>
        arg 2
        conv =>
          arg 2
          rw [rozznica]
          rw [summa]
          rw [PrawaL.PrzemiennoscKoniunkcji]
          rw [PrawaL.PrawRozdzielnosciI]
          conv =>
            arg 1
            rw [PrawaL.PrzemiennoscKoniunkcji]
            rw [←rozznica]
          arg 2
          rw [PrawaL.PrzemiennoscKoniunkcji]
          rw [←rozznica]
        arg 1
        rw [summa]
        rw [summa]
        rw [Zakon.LacznoscPrzekrojuZb]
        rw [PrawaL.PrzemiennoscAlternatywy]
        arg 2
        rw [PrawaL.PrzemiennoscAlternatywy]
        rw [←summa]
      arg 2
      conv =>
        arg 1
        rw [←summa]
        rw [PrawaL.PrzemiennoscKoniunkcji]
        rw [←przekroj]
        rw [(Zakon.PodzPrzPrzek ((A∩(B∩C))∪A) (B∩C∪A)).mp krok17]
    conv =>
      arg 2
      conv =>
        arg 2
        conv =>
          arg 2
          conv =>
            arg 2
            conv =>
              arg 2
              rw [rozznica]
              rw [przekroj]
              conv =>
                arg 1
                rw [PrawaL.PrzemiennoscKoniunkcji]
              rw [PrawaL.LaczanoscKoniunkcji]
              rw [PrawaL.PrawSprzecznosci]
              rw [PrawaL.PrawPochlaniania1]
            rw [PrawaL.PrawPochlaniania3]
        rw [PrawaL.PrawRozdzielnosciI]
        conv =>
          arg 1
          rw [summa]
          rw [PrawaL.PrawRozdzielnosciI]
          conv =>
            arg 2
            rw [rozznica]
            rw [PrawaL.PrzemiennoscKoniunkcji]
            rw [←PrawaL.LaczanoscKoniunkcji]
            rw [←przekroj]
            rw [←rozznica]
          rw [PrawaL.PrzemiennoscAlternatywy]
          rw [PrawaL.PrawRozdzielnosciII]
          conv =>
            arg 1
            rw [←summa]
            rw [(Zakon.PodzPrzSum (A∩C\(A\B)) (C\(A\B))).mp krok20]
          rw [PrawaL.PrawRozdzielnosciI]
          conv =>
            arg 1
            rw [PrawaL.PrzemiennoscKoniunkcji]
            rw [←przekroj]
            rw [(Zakon.PodzPrzPrzek (A∩C\(A\B)) (C\(A\B))).mp krok20]
          conv =>
            arg 2
            conv =>
              arg 1
              rw [rozznica]
              rw [rozznica]
              rw [PrawaL.PrawMorgana2]
              rw [←PrawaL.PrawPodwojnegoPrzeczenia]
              rw [PrawaL.PrawRozdzielnosciI]
              rw [←rozznica]
              rw [←przekroj]
          conv =>
            arg 1
            rw [rozznica]
            rw [przekroj]
            rw [rozznica]
            rw [PrawaL.PrawMorgana2]
            rw [←PrawaL.PrawPodwojnegoPrzeczenia]
            conv =>
              arg 1
              rw [←przekroj]
            rw [PrawaL.PrawRozdzielnosciI]
            conv =>
              arg 1
              rw [przekroj]
              rw [PrawaL.PrzemiennoscKoniunkcji]
              rw [←PrawaL.LaczanoscKoniunkcji]
              conv =>
                arg 1
                rw [PrawaL.PrzemiennoscKoniunkcji]
              rw [PrawaL.PrawSprzecznosci]
              rw [PrawaL.PrzemiennoscKoniunkcji]
              rw [PrawaL.PrawPochlaniania1]
            rw [PrawaL.PrzemiennoscAlternatywy]
            rw [PrawaL.PrawPochlaniania3]
            rw [przekroj]
            rw [PrawaL.LaczanoscKoniunkcji]
            conv =>
              arg 2
              rw [PrawaL.PrzemiennoscKoniunkcji]
              rw [←przekroj]
            rw [←przekroj]
          conv =>
            arg 2
            conv =>
              arg 1
              rw [Zakon.PrzemiennoscPrzekZb]
              rw [←summa]
            rw [PrawaL.PrzemiennoscKoniunkcji]
            rw [←przekroj]
            rw [(Zakon.PodzPrzPrzek (A∩(B∩C)) (C\A∪(B∩C))).mp krok22]
        rw [PrawaL.PrawTaut1]
        conv =>
          arg 2
          rw [rozznica]
          rw [PrawaL.LaczanoscKoniunkcji]
          conv =>
            arg 2
            rw [PrawaL.PrzemiennoscKoniunkcji]
            rw [PrawaL.PrawSprzecznosci]
          rw [PrawaL.PrawPochlaniania1]
        rw [PrawaL.PrawPochlaniania3]
        rw [←Zakon.LacznoscPrzekrojuZb]
    rw [←summa]
    rw [←summa]
    rw [←Zakon.LacznoscSumZb]
theorem LacznoscRoznicySymetrycznej (A B C : Zbior.{u}) : A∸(B∸C) = (A∸B)∸C := by
  apply eksten
  intro x
  rw [RozSymLacznoscI]
  rw [SymRozdoS]
namespace PrawaL
theorem PrawRozlacznosciWzgKoniunkcjiP : (p∨q)∧r ≡ p∧r ∨ q∧r := by
  conv =>
  lhs
  rw [PrawaL.PrzemiennoscKoniunkcji]
  rw [PrawaL.PrawRozdzielnosciI]
  conv =>
    arg 1
    rw [PrawaL.PrzemiennoscKoniunkcji]
  arg 2
  rw [PrawaL.PrzemiennoscKoniunkcji]
theorem PrawRozlacznosciWzgAlternatywyP : (p∧q)∨r ≡ (p∨r) ∧ (q∨r) := by
  conv =>
    lhs
    rw [PrawaL.PrzemiennoscAlternatywy]
    rw [PrawaL.PrawRozdzielnosciII]
    conv =>
      arg 1
      rw [PrawaL.PrzemiennoscAlternatywy]
    arg 2
    rw [PrawaL.PrzemiennoscAlternatywy]
theorem MojeTwierdzenie (n : Nat) : n + 0 = n := by
  induction n with
    | zero =>
      simp
    | succ n base =>
      simp
theorem MojeTw2 (n:Nat) : 0 + n = n := by
  induction n with
    | zero =>
      rfl
    | succ n base =>
      calc
        0 + (n + 1) = (0 + n) + 1 := by rfl
        _           = n + 1 := by rw[base]
end PrawaL
#check PrawaL.PrawRozlacznosciWzgKoniunkcjiP

/-@[simp] noncomputable def RodzinaZb : (List Zbior.{u}) → Zbior.{u}
  | List.nil => Ø
  | List.cons A RZ => A∪(RodzinaZb RZ)
prefix:65 (priority := high) "⋃" => RodzinaZb
variable (A B C D E: Zbior.{u}) (G H I J : Zbior.{u})
#check  ⋃ [A, B, C ,E]
noncomputable def FZb := ⋃ [A, B, C, E]
noncomputable def GZb := ⋃[G,H,I,J]
@[simp] noncomputable def SumaRodzinZb (K L :List Zbior.{u}) : Zbior.{u} :=
  match K with
    | List.nil => ⋃ L
    | List.cons A Rodz => A∪(SumaRodzinZb Rodz L)
#check FZb A B C E
infix:65 (priority := high) "⊔" => SumaRodzinZb-/
def IstniejeDokladnieJeden {α : Type u} (p : α → Prop) : Prop :=
  ∃ x, p x ∧ (∀ y, p y → y = x)
notation (priority := high) "∃! " x " : " t " , " p => IstniejeDokladnieJeden (fun (x : t) => p)
theorem RozdzielnoscPrzekrojuWzglRoznicySymetryczne (A B C : Zbior.{u}) : A∩(B∸C) = (A∩B)∸(A∩C) := by
  rw [RozSym]
  rw [PrawRozdzielnosciZbI A (B\C) (C\B)]
  rw [PrawRozdzielnosciPrzekrojuWzglOdejm]
  rw [Zakon.PrzemiennoscPrzekZb]
  rw [←PrawRozdzielnosciPrzekrojuWzglOdejm]
  rw [PrawOdejmowaniaZbIII]
  rw [PrawRozdzielnosciPrzekrojuWzglOdejm]
  rw [Zakon.PrzemiennoscPrzekZb]
  rw [PrawRozdzielnosciPrzekrojuWzglOdejm]
  rw [Zakon.PrzemiennoscPrzekZb A C]
  rw [←PrawRozdzielnosciPrzekrojuWzglOdejm C A B]
  rw [PrawOdejmowaniaZbIII A B]
  rw [PrawRozdzielnosciPrzekrojuWzglOdejm]
  rw [Zakon.PrzemiennoscPrzekZb C A]
  rw [←RozSym]
theorem RoznicaSymetrycznaZPustym (A : Zbior.{u}) : A∸Ø = A := by
  rw [RozSym]
  rw [Zakon.PustMZb]
  rw [Zakon.ZbMPust]
  rw [Zakon.SumaZPust]
theorem RoznicaSymetrycznaWzglSamejSiebie (A : Zbior.{u}) : A∸A = Ø := by
  rw [RozSym]
  rw [Zakon.OdejmowanieSamejOdSiebie]
  rw [Zakon.SumaZPust]
theorem DzialanieOdwrotneWZbiorach (A C : Zbior.{u}) : ∃! B:Zbior.{u}, A∸B=C := by
  unfold IstniejeDokladnieJeden
  exists (A∸C)
  constructor
  · calc
      A∸(A∸C) = (A∸A)∸C := by rw [LacznoscRoznicySymetrycznej]
      _ = Ø ∸ C := by rw [RoznicaSymetrycznaWzglSamejSiebie]
      _ = C∸Ø := by rw [RozSymPrzemiennosc]
      _ = C := by rw [RoznicaSymetrycznaZPustym]
  · intro H Rozh
    calc
      H = H ∸ Ø := by rw [RoznicaSymetrycznaZPustym]
      _ = H ∸ (C∸C) := by rw [RoznicaSymetrycznaWzglSamejSiebie]
      _ = (H∸C)∸C := by rw [LacznoscRoznicySymetrycznej]
      _ = (H∸(A∸H))∸C := by rw [Rozh]
      _ = (H∸(H∸A)) ∸ C := by rw [RozSymPrzemiennosc H A]
      _ = ((H∸H)∸A)∸C := by rw [LacznoscRoznicySymetrycznej]
      _ = (Ø∸A)∸C := by rw [RoznicaSymetrycznaWzglSamejSiebie]
      _ = (A∸Ø)∸C := by rw [RozSymPrzemiennosc A Ø]
      _ = A∸C := by rw [RoznicaSymetrycznaZPustym]
theorem SumaPrzezRozniceSymetryczna (A B : Zbior.{u}) : A∪B = A∸B∸(A∩B) := by
  rw [SymRozdoS]
  have krok1 : A∩B⊆B := Zakon.PrzekrojWZbP A B
  have krok2 : A∩B⊆A := Zakon.PrzekrojWZbL A B
  have krok3 : A∩B⊆A∪B := PrzechZb (A∩B) A (A∪B) (And.intro krok2 (Zakon.ZbiorWSumL A B))
  have krok4 : B\A⊆B := Zakon.RozWZbL B A
  rw [Zakon.PrzemiennoscSumZb B (A∩B)]
  rw [(Zakon.PodzPrzSum (A∩B) B).mp krok1]
  rw [Zakon.PrzemiennoscSumZb A (A∩B)]
  rw [(Zakon.PodzPrzSum (A∩B) A).mp krok2]
  rw [(Zakon.PodzbOdNadzbioru (A∩B) (A∪B)) krok3]
  rw [Zakon.SumaZPust]
  rw [Zakon.II]
  apply eksten
  intro x
  conv =>
    arg 2
    rw [summa]
    rw [summa]
    rw [PrawaL.LacznoscAlternatywy]
    rw [przekroj]
    rw [PrawaL.PrawRozdzielnosciII]
    rw [rozznica]
    rw [rozznica]
    conv =>
      arg 2
      rw [PrawaL.PrzemiennoscAlternatywy]
      rw [PrawaL.PrawRozdzielnosciII]
      rw [PrawaL.PrawWylaczonegoSrodka]
      rw [PrawaL.PrawPochlaniania2]
      rw [←summa]
      arg 2
      rw [←rozznica]
      rw [←summa]
      arg 2
      rw [(Zakon.PodzPrzSum (B\A) B).mp krok4]
    rw [←przekroj]
    conv =>
      arg 2
      arg 2
      rw [Zakon.PrzemiennoscPrzekZb]
      rw [(Zakon.PodzPrzPrzek B (A∪B)).mp (Zakon.ZbiorWSumP A B)]
    rw [PrawaL.PrawRozlacznosciWzgAlternatywyP]
    arg 2
    rw [PrawaL.PrzemiennoscAlternatywy]
    rw [PrawaL.PrawWylaczonegoSrodka]
  rw [PrawaL.PrawPochlaniania2]
  rw [←summa]
theorem RoznicaPrzezRozniceSym (A B : Zbior.{u}) : A\B = A∸(A∩B) := by
  rw [RozSym]
  have krok1 : A∩B⊆A := Zakon.PrzekrojWZbL A B
  have krok2 : A∩B\A = Ø := (Zakon.PodzbOdNadzbioru (A∩B) A) krok1
  rw [krok2]
  rw [Zakon.SumaZPust]
  apply eksten
  intro x
  rw [rozznica]
  rw [rozznica]
  rw [przekroj]
  rw [PrawaL.PrawMorgana2]
  rw [PrawaL.PrawRozdzielnosciI]
  rw [PrawaL.PrawSprzecznosci]
  rw [@PrawaL.PrzemiennoscAlternatywy]
  rw [PrawaL.PrawPochlaniania3]
theorem DlaZbiorowRozlacznychSumaPrzezRozSym (A B : Zbior.{u}) (h : A∩B = Ø) :
A∪B = A∸B := by
  rw [SumaPrzezRozniceSymetryczna]
  rw [h]
  rw [RoznicaSymetrycznaZPustym]
theorem RoznicaSymetrycznaWSumie (A B : Zbior.{u}) : A∸B⊆A∪B := by
  rw [podzbior]
  intro x hAB
  rw [RozSym] at hAB
  rw [summa] at hAB
  rcases hAB with h_left | h_right
  · have krok1 : x∈A := by
      have f1 : A\B⊆A := Zakon.RozWZbL A B
      rw [podzbior] at f1
      exact (f1 x h_left)
    have krok2 : x∈A ∨ x∈B := Or.inl krok1
    rw [←summa] at krok2
    exact krok2
  · have krok3 : x∈B := by
      have f2 : B\A⊆B := Zakon.RozWZbL B A
      rw [podzbior] at f2
      exact (f2 x h_right)
    have krok4 : x∈A ∨ x∈B := Or.inr krok3
    rw [←summa] at krok4
    exact krok4

def Ideal (X I : Zbior.{u}) : Prop :=
  (∃Y:Zbior.{u}, (Y∈I)) ∧
  (∀Y:Zbior.{u}, Y∈I → Y⊆X) ∧
  (∀(K Z :Zbior.{u}), (K⊆Z)∧(Z∈I) → (K∈I)) ∧
  (∀(K Z : Zbior.{u}), (K∈I)∧(Z∈I) → (K∪Z∈I))
def PrzystawanieDoIdealu (A B I: Zbior.{u}):= (A∸B∈I)
notation:50 A "≐" B "(mod "I")" => PrzystawanieDoIdealu A B I
variable (A B X I : Zbior.{u})
#check A≐B(modI)
theorem ZbiorPustyPodzbioremKazdegoZbioru: ∀A:Zbior.{u}, Ø⊆A := by
  intro A
  rw [podzbior]
  intro x
  intro hO
  rw [WPust] at hO
  exact False.elim hO
theorem ZwrotnoscPrrzystawania (A I X: Zbior.{u}) (h : Ideal X I): A≐A(mod I) := by
  rw [PrzystawanieDoIdealu]
  rw [RoznicaSymetrycznaWzglSamejSiebie]
  obtain ⟨hY,hY_sub_X,hKZ_wyn,hKZ_el⟩ := h
  obtain ⟨Y,hY_in_I⟩ := hY
  have krok1 : Ø⊆Y := ZbiorPustyPodzbioremKazdegoZbioru Y
  have krok2 : Ø∈I := hKZ_wyn Ø Y (And.intro krok1 hY_in_I)
  exact krok2
theorem SymetriaPrzystawania (A B X I : Zbior.{u}) (h : Ideal X I) : (A≐B(mod I)) → (B≐A(mod I)) := by
  intro hAB
  rw [PrzystawanieDoIdealu] at hAB
  rw [RozSymPrzemiennosc] at hAB
  rw [←PrzystawanieDoIdealu] at hAB
  exact hAB
theorem SymetriaPrzystawaniaPrzezEquiv (A B X I : Zbior.{u}) (h : Ideal X I) :
(A≐B(mod I)) ≡ (B≐A(mod I)) := by
  apply Iff.intro
  · intro hAB
    exact (SymetriaPrzystawania A B X I h hAB)
  · intro hBA
    exact (SymetriaPrzystawania B A X I h hBA)
theorem PrzechodnioscPrzystawania (A B C X I : Zbior.{u}) (h : Ideal X I) :
(A≐B(mod I)) ∧ (B≐C(mod I)) → (A≐C(mod I)) := by
  intro hAB_BC
  obtain ⟨hY, hY_in_X,h_podzb, h_sum⟩ := h
  rw [PrzystawanieDoIdealu] at hAB_BC
  rw [PrzystawanieDoIdealu] at hAB_BC
  --have krok1 : (A∸B)∪(B∸C)∈I := h_sum (A∸B) (B∸C) hAB_BC
  have krok2 : A∸C = (A∸B)∸(B∸C) := by
    calc
      A∸C = A∸C∸Ø := by rw [RoznicaSymetrycznaZPustym]
      _ = A∸(C∸Ø) := by rw [LacznoscRoznicySymetrycznej]
      _ = A∸(Ø∸C) := by rw [RozSymPrzemiennosc C Ø]
      _ = A∸(B∸B∸C) := by rw [RoznicaSymetrycznaWzglSamejSiebie]
      _ = A∸(B∸(B∸C)) := by rw [LacznoscRoznicySymetrycznej B B C]
      _ = (A∸B)∸(B∸C) := by rw [LacznoscRoznicySymetrycznej]
  have krok3 : (A∸B)∸(B∸C)⊆(A∸B)∪(B∸C) := RoznicaSymetrycznaWSumie (A∸B) (B∸C)
  have krok4 : (A∸B)∪(B∸C)∈I := h_sum (A∸B) (B∸C) hAB_BC
  rw [←krok2] at krok3
  exact (h_podzb (A∸C) (A∸B∪B∸C) (And.intro krok3 krok4))
theorem RozlacznoscPrzezPrzystawanie (A B X I : Zbior.{u}) (h : Ideal X I) :
A∩B=Ø → A∩B≐Ø(mod I) := by
  intro hAB
  rw [hAB]
  exact (ZwrotnoscPrrzystawania Ø I X h)
theorem PodzbiorPrzezPrzystawanie (A B X I: Zbior.{u}) (h : Ideal X I) :
A⊆B → A\B≐Ø(mod I) := by
  intro hA_in_B
  rw [Zakon.PodzbOdNadzbioru A B hA_in_B]
  exact (ZwrotnoscPrrzystawania Ø I X h)
def Filtr (X 𝔽 : Zbior.{u}) : Prop :=
  (∃Y:Zbior.{u},(Y∈𝔽)) ∧
  (∀Y:Zbior.{u}, Y∈𝔽 → Y⊆X) ∧
  (∀(Y Z : Zbior.{u}), (Y⊆Z) ∧ (Y∈𝔽) → Z∈𝔽) ∧
  (∀(Y Z : Zbior.{u}), Y∈𝔽 ∧ Z∈𝔽 → Y∩Z∈𝔽)
def PrzystawanieDoFiltru  (A B X 𝔽: Zbior.{u}) :=((X\A)∪B∈𝔽 ∧ (X\B)∪A∈𝔽)

notation:50  A "≐" B "(modF "𝔽"|Przes:"X")" => PrzystawanieDoFiltru A B X 𝔽

theorem PrzystawanieDoFiltruII (X A B 𝔽 : Zbior.{u}) (hA : A⊆X) (hB : B⊆X) (filtr : Filtr X 𝔽)
: A≐B(modF 𝔽|Przes:X) ≡ X\(A∪B)∪(A∩B)∈𝔽 := by
  rw [PrawMorganaZbII]
  rw [Zakon.PrzemiennoscSumZb]
  rw [PrawRozdzielnosciZbII]
  rw [Zakon.PrzemiennoscSumZb]
  rw [PrawRozdzielnosciZbII]
  rw [Zakon.PrzemiennoscSumZb (A∩B) (X\B)]
  rw [PrawRozdzielnosciZbII]
  rw [Zakon.PrzemiennoscSumZb]
  rw [PrawOdejmowaniaZbI]
  rw [Zakon.PrzemiennoscSumZb (X\B) B]
  rw [PrawOdejmowaniaZbI]
  rw [(Zakon.PodzPrzSum A X).mp hA]
  rw [(Zakon.PodzPrzSum B X).mp hB]
  rw [Zakon.PrzemiennoscPrzekZb]
  rw [Zakon.LacznoscPrzekrojuZb]
  have krok1 :X\A⊆X := Zakon.RozWZbL X A
  conv =>
    arg 2
    conv =>
      arg 1
      conv =>
        arg 2
        rw [←Zakon.LacznoscPrzekrojuZb]
        rw [Zakon.II]
        rw [PrawRozdzielnosciZbI]
        rw [Zakon.PrzemiennoscPrzekZb]
        rw [(@Zakon.PodzPrzPrzek (X\A) X).mp krok1]
        rw [Zakon.PrzemiennoscPrzekZb]
        rw [(@Zakon.PodzPrzPrzek B X).mp hB]
  rw [PrzystawanieDoFiltru]
  obtain ⟨HY, hY_in_X, R1, R2⟩ := filtr
  apply Iff.intro
  · intro f1
    rw [Zakon.PrzemiennoscPrzekZb]
    exact (R2 (X\A∪B) (X\B∪A) f1)
  · intro f2
    have krok4 : X\A∪B∈𝔽 := R1 ((X\B∪A)∩(X\A∪B)) (X\A∪B) (And.intro (Zakon.PrzekrojWZbP (X\B∪A) (X\A∪B)) f2)
    have krok5 : X\B∪A∈𝔽 := R1 ((X\B∪A)∩(X\A∪B)) (X\B∪A) (And.intro (Zakon.PrzekrojWZbL (X\B∪A) (X\A∪B)) f2)
    exact (And.intro krok4 krok5)
structure Przestrzen (X : Zbior.{u}) where
  z : Zbior.{u}
  p : z⊆X
noncomputable def Dopelnienie (A X : Zbior.{u}) := X\A
notation:75 "∁{"A"|"X"}" => Dopelnienie A X
variable (X A x: Zbior.{u}) (P : Zbior.{u} → Prop)
#check ∁{∁{A|X}|X}

theorem DopelnienieDopelnieniaWPrzestrz (A X : Zbior.{u}) (h : A⊆X) : ∁{∁{A|X}|X} = A := by
  rw [Dopelnienie]
  rw [Dopelnienie]
  rw [OdejmowanieOdRoznic]
  rw [Zakon.OdejmowanieSamejOdSiebie]
  rw [Zakon.PrzemiennoscSumZb]
  rw [Zakon.SumaZPust]
  rw [Zakon.PrzemiennoscPrzekZb]
  rw [(Zakon.PodzPrzPrzek A X).mp h]
theorem PrawInkluzjiWPrzestrz (A B X : Zbior.{u}) (h : A⊆X) (h2 : B⊆X) : A⊆B ≡ ∁{B|X}⊆∁{A|X} := by
  apply Iff.intro
  · intro hAB
    rw [Dopelnienie]
    rw [Dopelnienie]
    exact ((StosunekInkluzjiIV X A B) hAB)
  · intro hD
    rw [Dopelnienie] at hD
    rw [Dopelnienie] at hD
    rw [podzbior] at hD
    rw [podzbior]
    intro x hA
    have krok1 : x∈X := h x hA
    apply Classical.byContradiction
    intro hNB
    have krok2 : x∈X\B := by
      rw [rozznica]
      exact (And.intro krok1 hNB)
    have krok3 : x∈X\A := hD x krok2
    have krok4 : x∈A ∧ x∈X\A := And.intro hA krok3
    rw [rozznica] at krok4
    rw [PrawaL.PrzemiennoscKoniunkcji] at krok4
    rw [PrawaL.LaczanoscKoniunkcji] at krok4
    rw [@PrawaL.PrzemiennoscKoniunkcji (¬x∈A) (x∈A) ] at krok4
    rw [PrawaL.PrawSprzecznosci] at krok4
    rw [PrawaL.PrawPochlaniania1] at krok4
    exact krok4
theorem OdejmowaniePrzezPrzekrojZDopelnieniem (A B X : Zbior.{u}) (h:A⊆X) (h2:B⊆X):
A\B = A∩(∁{B|X}) := by
  rw [Dopelnienie]
  apply eksten
  intro x
  rw [przekroj]
  rw [rozznica]
  rw [rozznica]
  conv =>
    arg 2
    rw [←PrawaL.LaczanoscKoniunkcji]
    arg 1
    rw [PrawaL.PrzemiennoscKoniunkcji]
  rw [PrawaL.LaczanoscKoniunkcji]
  conv =>
    arg 2
    conv =>
      arg 2
      rw [←rozznica]
    rw [←przekroj]
    rw [Zakon.PrzemiennoscPrzekZb]
  have krok1 : A\B⊆X := PrzechZb (A\B) A X (And.intro (Zakon.RozWZbL A B) h)
  conv =>
    arg 2
    rhs
    rw [(Zakon.PodzPrzPrzek (A\B) X).mp krok1]
  rw [←rozznica]
theorem OdejmowaniePrzezOdejmowanieDopelnien (A B X : Zbior.{u}) (h : A⊆X) (h2:B⊆X) :
A\B = ∁{B|X}\∁{A|X} := by
  rw [OdejmowaniePrzezPrzekrojZDopelnieniem A B X h h2]
  rw [Zakon.PrzemiennoscPrzekZb]
  rw [←DopelnienieDopelnieniaWPrzestrz A X h]
  rw [←OdejmowaniePrzezPrzekrojZDopelnieniem]
  rw [DopelnienieDopelnieniaWPrzestrz A X h]
  rw [Dopelnienie]
  · exact (Zakon.RozWZbL X B)
  · rw [Dopelnienie]
    exact (Zakon.RozWZbL X A)
theorem PrawaMorganaDlaDopelnien1 (A B X : Zbior.{u}) (h : A⊆X) (h2 : B⊆X) : ∁{A∩B|X} =
∁{A|X}∪∁{B|X} := by
  rw [Dopelnienie]
  rw [PrawMorganaZbI]
  rw [←Dopelnienie]
  rw [←Dopelnienie]
theorem PrawaMorganaDlaDopelnien2 (A B X : Zbior.{u}) (h : A⊆X) (h2 : B⊆X) :
∁{A∪B|X} = ∁{A|X}∩∁{B|X} := by
  rw [Dopelnienie]
  rw [PrawMorganaZbII]
  rw [←Dopelnienie]
  rw [←Dopelnienie]
theorem OdejmowaniePrzezPodwojneDopelnienieSumy (A B X : Zbior.{u}) (h : A⊆X) (h2 : B⊆X):
A\B = ∁{∁{A|X}∪B|X} := by
  have krok1 : ∁{A|X} ⊆ X := by
    rw [Dopelnienie]
    exact @Zakon.RozWZbL X A
  rw [@PrawaMorganaDlaDopelnien2 (∁{A|X}) B X krok1 h2]
  rw [DopelnienieDopelnieniaWPrzestrz A X h]
  rw [←OdejmowaniePrzezPrzekrojZDopelnieniem A B X h h2]
noncomputable def DzielenieZbiorow {X : Zbior.{u}} (A B : Zbior.{u}) {h : A⊆X} {h2:B⊆X}: Zbior.{u}:=
A∪∁{B|X}
infix:70 (priority := high) ":" => DzielenieZbiorow
#check A:B
