universe u
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
theorem ImpPrzezAlt : (p→q) ≡ (¬p∨q) := by
    apply Iff.intro
    intro h
    by_cases hp:p
    exact Or.inr (h hp)
    exact Or.inl hp
    intro h hp
    have krok1 := Or.elim h (fun (k : ¬p) => False.elim (k hp)) (fun (hq:q) => hq)
    exact krok1
theorem NegImpl : ¬(p → q) ≡ p∧¬q := by
    apply Iff.intro
    intro h
    rw [ImpPrzezAlt, PrawaL.PrawMorgana1,←PrawaL.PrawPodwojnegoPrzeczenia] at h
    exact h
    intro h hn
    exact h.right (hn h.left)
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
theorem PrawWnioskowaniaZAlternatyw (p q : Prop) : (¬p ∧ (p ∨ q)) → q := by
    intro h
    have ⟨h1,h2⟩ := h
    cases h2 with
    | inl hnP =>
        exact False.elim (h1 hnP)
    | inr hQ  =>
        exact hQ
end PrawaL
variable (Num : Type u)
inductive SierpNat : Type  where
    | zero : SierpNat
    | S : SierpNat → SierpNat
    deriving Repr
def AddSierpNat (n m : SierpNat) : SierpNat :=
    match m with
        | SierpNat.zero => n
        | SierpNat.S k => SierpNat.S (AddSierpNat n k)
abbrev zero := SierpNat.zero
abbrev S := SierpNat.S
infixl:60 (priority := high) "+" => AddSierpNat
#check Zero
def formNat : Nat → SierpNat
    | 0 => zero
    | Nat.succ n => S (formNat n)
instance {n : Nat} : OfNat SierpNat n where
    ofNat := formNat n
@[simp] theorem PlusZero : ∀a:SierpNat, a + 0 = a := by
    intro a
    induction a with
        | zero =>
            rfl
        | S a base =>
            calc
                S a + 0 = S (a + 0) := by rfl
                _ = S a := by rw [base]
def Set (α : Type u):= α → Prop
def nalezy {α : Type u} (x : α) (f : Set α): Prop := f x
infix:75 (priority := high) "∈" => nalezy
axiom A1 : ∀n:SierpNat, S n ≠ 0
axiom A2 : ∀(n m : SierpNat), (S n = S m) → n = m
theorem lemmaDodawaniaNast : ∀(n m : SierpNat), S n + m = S (n+m) := by
    intro n m
    induction m with
        | zero =>
            calc
                S n + 0 = S n := by rfl
        | S m base =>
            calc
                S n + S m = S (S n + m) := by rfl
                _ = S (S (n + m)) := by rw [base]
                _ = S (n + S m) := by rfl
@[simp] theorem PlusZeroII : ∀a:SierpNat, 0 + a = a := by
    intro a
    induction a with
        | zero =>
            rfl
        | S a base =>
            calc
                0 + S a = S (0 + a) := by rfl
                _ = S a := by rw [base]
theorem PrzemiennoscDodawania : ∀(n m : SierpNat), n+m = m+n := by
    intro n m
    induction m with
        | zero =>
            calc
                n + 0 = n := by rw [PlusZero]
                _ = 0 + n := by rw [PlusZeroII]
        | S m base =>
            calc
                n + S m = S (n + m) := by rfl
                _ = S (m + n) := by rw [base]
                _ = S m + n := by rw [lemmaDodawaniaNast]
theorem Wlasnosc1 : zero ≠ S zero := by
    rw [Ne.eq_1]
    apply Classical.byContradiction
    intro h
    rw [Classical.not_not] at h
    rw [eq_comm] at h
    exact (A1 zero h)
theorem Wlasnosc2 (n : SierpNat) : n ≠ S n → S n ≠ S (S n) := by
    rw [Ne.eq_1]
    rw [Ne.eq_1]
    have krok1 : ∀(p q : Prop), (¬q → ¬p) → (p → q) := by
        intro p q h hp
        apply Classical.byContradiction
        intro hnq
        exact (h hnq hp)
    apply krok1
    rw [Classical.not_not]
    rw [Classical.not_not]
    intro h2
    exact (@A2 n (S n) h2)
theorem Twierdzenie1 (n : SierpNat) : n ≠ S n := by
    induction n with
        | zero =>
            exact Wlasnosc1
        | S n base =>
            exact @Wlasnosc2 n base
def Z : Set SierpNat := fun n:SierpNat => n=0 ∨ ∃m:SierpNat, n = S m
theorem Indukcja (n : SierpNat) : n∈Z := by
    induction n with
        | zero =>
            exact Or.inl rfl
        | S k base =>
            exact Or.inr (Exists.intro k rfl)

theorem Twierdzenie2 (n : SierpNat) : n ≠ 0 → ∃m:SierpNat, n = S m := by
    intro h
    have hZ := Indukcja n
    apply Or.elim hZ
    intro hz
    exact False.elim (h hz)
    intro k
    exact k
theorem NastepnikPrzezSume (n : SierpNat) : S n = n + S 0 := by
    calc
        S n = S (n + 0) := by rw [PlusZero]
theorem ZamianaNastepnika (n m : SierpNat) : n + S m = S n + m := by
    rw [PrzemiennoscDodawania, lemmaDodawaniaNast, PrzemiennoscDodawania, ←lemmaDodawaniaNast]
theorem PrzemiennoscZZerem (n : SierpNat) : n + 0 = 0 + n := by
    induction n with
        | zero =>
            rfl
        | S n base =>
            rw [lemmaDodawaniaNast, PlusZero, PlusZeroII]
theorem LacznoscDodawania (n m k : SierpNat) : n + (m + k) = (n + m) + k := by
    induction k with
        | zero =>
            rfl
        | S k base =>
            rw [ZamianaNastepnika, lemmaDodawaniaNast, ZamianaNastepnika, lemmaDodawaniaNast, base]
            rw [←lemmaDodawaniaNast, ←ZamianaNastepnika]
theorem LacznoscDodawania2 (n m k l : SierpNat) : n + (m + (k + l)) = ((n + m) + k) + l := by
    rw [LacznoscDodawania m k l, LacznoscDodawania, LacznoscDodawania]
@[simp] def Δ (n : SierpNat) :=
    match n with
        | .zero => zero
        | SierpNat.S n => Δ n + SierpNat.S n
theorem PrawoWnioskowaniaZera (n m : SierpNat) : n + m = n → m=0 := by
    induction n with
        | zero =>
            intro k
            change 0 + m = 0 at k
            rw [PlusZeroII m] at k
            exact k
        | S n base =>
            intro k2
            rw [lemmaDodawaniaNast] at k2
            change S (n+m) = S n at k2
            have krok1 : n+m = n := A2 (n+m) n k2
            exact base krok1
theorem zadanie1 (n : SierpNat): S (Δ n) = Δ (S n) → n = 0 := by
    intro h
    have krok1 : Δ (S n) = Δ n + S n := by rfl
    have krok2 : Δ n + S n = S (Δ n + n) := by rw [ZamianaNastepnika, lemmaDodawaniaNast]
    have krok3 : Δ n  = Δ n + n := by
        rw [krok1] at h
        rw [krok2] at h
        exact (@A2 (Δ n) (Δ n + n) h)
    rw [Eq.comm] at krok3
    exact PrawoWnioskowaniaZera (Δ n) n krok3
@[simp] def Mnozenie (n m : SierpNat) : SierpNat :=
    match m with
        | SierpNat.zero => SierpNat.zero
        | SierpNat.S k => Mnozenie n k + n
infix:70 (priority := high) "*" => Mnozenie
variable (k g : SierpNat)
@[simp] def AlternatywaWykluczajaca (p q : Prop) : Prop := (p ∧ ¬q) ∨ (q ∧ ¬p)
infixl:45 (priority := high) "⊻" => AlternatywaWykluczajaca
theorem AlternatywaWykluczajacaDlaTrzech (p q r : Prop) : p ⊻ q ⊻ r ≡ (p ∧ ¬q ∧ ¬r) ∨ (q ∧ ¬p ∧ ¬r) ∨
(r ∧ ¬p ∧ ¬q) ∨ (p∧q∧r):= by
    rw [AlternatywaWykluczajaca, AlternatywaWykluczajaca, PrawaL.PrzemiennoscKoniunkcji, PrawaL.PrawMorgana1]
    rw [PrawaL.PrawMorgana2, PrawaL.PrawMorgana2, ←PrawaL.PrawPodwojnegoPrzeczenia, ←PrawaL.PrawPodwojnegoPrzeczenia]
    rw [PrawaL.PrawRozdzielnosciI, PrawaL.PrawRozdzielnosciI, @PrawaL.PrzemiennoscKoniunkcji (¬p∨q) ¬q]
    rw [@PrawaL.PrawRozdzielnosciI ¬q, @PrawaL.PrzemiennoscKoniunkcji (¬q) q, PrawaL.PrawSprzecznosci, PrawaL.PrawPochlaniania3]
    rw [@PrawaL.PrzemiennoscKoniunkcji (¬p∨q) p, @PrawaL.PrawRozdzielnosciI p (¬p) q, PrawaL.PrawSprzecznosci,←PrawaL.LacznoscAlternatywy, @PrawaL.PrawPochlaniania3 (¬q∧¬p)]
    rw [PrawaL.PrawRozdzielnosciI, ←PrawaL.LaczanoscKoniunkcji, @PrawaL.PrzemiennoscKoniunkcji ¬r, PrawaL.LaczanoscKoniunkcji]
    rw [@PrawaL.PrzemiennoscKoniunkcji (¬r) (¬q), @PrawaL.PrzemiennoscKoniunkcji (¬r) (q∧¬p), PrawaL.LaczanoscKoniunkcji]
    rw [@PrawaL.PrzemiennoscKoniunkcji (¬q) (¬p), @PrawaL.PrzemiennoscKoniunkcji r (p∧q), PrawaL.LaczanoscKoniunkcji]
    rw [PrawaL.LacznoscAlternatywy]
theorem MnozenieNastZera (n : SierpNat) : S zero * n = n := by
    induction n with
        | zero =>
            rfl
        | S n base =>
            simp
            rw [base]
            change n + S 0 = S n
            rw [←NastepnikPrzezSume]
theorem RozdzielnoscMnozeniaP (n m k : SierpNat) : (n + m)*k = n*k + m*k := by
    induction k with
        | zero =>
            rfl
        | S k base =>
            change (n+m) * S k = n*S k + m*S k
            simp
            rw [base]
            rw [LacznoscDodawania]
            rw [PrzemiennoscDodawania (m*k)]
            rw [←LacznoscDodawania2]
            rw [PrzemiennoscDodawania (m*k)]
            rw [LacznoscDodawania]
            rw [LacznoscDodawania]
            rw [LacznoscDodawania]
theorem MnozeniePrzezZero (n : SierpNat) : 0 * n = 0 := by
    induction n with
        | zero =>
            rfl
        | S n base =>
            simp
            exact base
theorem PrzemiennoscMnozenia (n m : SierpNat) : n*m=m*n := by
    induction m with
        | zero =>
            simp
            change 0 = 0*n
            rw [MnozeniePrzezZero]
        | S m base =>
            change n*S m = S m * n
            simp
            rw [NastepnikPrzezSume]
            rw [RozdzielnoscMnozeniaP]
            change n*m + n = m*n + S zero * n
            rw [MnozenieNastZera]
            rw [base]
theorem RozdzielnoscMnozeniaL (n m k : SierpNat) : n*(m+k) = n*m + n*k := by
    rw [PrzemiennoscMnozenia]
    rw [RozdzielnoscMnozeniaP]
    rw [PrzemiennoscMnozenia]
    rw [PrzemiennoscMnozenia n k]
theorem LacznoscMnozenia2 (n m k : SierpNat) : n*(m*k) = (n*m)*k := by
    induction k with
        | zero =>
            rfl
        | S k base =>
            simp
            rw [PrzemiennoscMnozenia]
            rw [RozdzielnoscMnozeniaP]
            rw [←base]
            rw [PrzemiennoscMnozenia]
            rw [PrzemiennoscMnozenia m n]
theorem PrawMnozenia (n m :SierpNat) :n*S m = n*m + n := by rfl
theorem IstnienieJednosci (n : SierpNat) : 1*n = n := by
    induction n with
        | zero =>
            rfl
        | S k base =>
            rw [PrawMnozenia]
            rw [base]
            rfl
@[simp] def Silnia (n : SierpNat) : SierpNat :=
    match n with
        | SierpNat.zero => SierpNat.S zero
        | SierpNat.S k => Mnozenie (Silnia k) (SierpNat.S k)
notation:80 A"!" => Silnia A
#eval (S (S (S zero))) !
@[simp] def Poprzednik (n : SierpNat) : SierpNat :=
    match n with
        | SierpNat.zero => SierpNat.zero
        | SierpNat.S n => n
prefix:80 "P" => Poprzednik
theorem PrawMorgana1 {p q : Prop} : ¬(p∨q) ↔ (¬p∧¬q) :=
  Iff.intro
    (fun (h1 : ¬(p∨q)) =>
      have k1 : ¬p := fun (hp:p) => h1 (Or.inl hp)
      have k2 : ¬q := fun (hq:q) => h1 (Or.inr hq)
    And.intro k1 k2)
    (fun (h2: ¬p∧¬q) => fun (hpq : p ∨ q) =>
    Or.elim hpq (fun (hp:p) => h2.left hp) (fun (hq:q) => h2.right hq))
@[simp] def OdejmowanieOgraniczone (n m : SierpNat) : SierpNat :=
    match m with
        | .zero => n
        | .S m => P OdejmowanieOgraniczone n m
infixl:70 "∸" => OdejmowanieOgraniczone
theorem SkracanieNastepnikowPrzyOdejm (n m : SierpNat) : S n ∸ S m = n ∸ m := by
    induction m with
        | zero =>
            rfl
        | S m base =>
            rw [OdejmowanieOgraniczone]
            change P( S n ∸ S m) = n ∸ S m
            rw [base]
            rw [←OdejmowanieOgraniczone]
theorem SkracanieDodawaniaPrzezOdejm (n m : SierpNat) : (n+m)∸n = m := by
    induction n with
        | zero =>
            simp
            change 0 + m = m
            rw [PlusZeroII]
        | S n base =>
            change (S n + m)∸(S n) = m
            rw [lemmaDodawaniaNast]
            rw [SkracanieNastepnikowPrzyOdejm]
            exact base
theorem OdejmowanieOgraniczoneTychSamych (n : SierpNat) : n∸n = 0 := by
    induction n with
        | zero =>
            rfl
        | S n base =>
            rw [SkracanieNastepnikowPrzyOdejm]
            exact base
theorem OdejmowanieOgraniczoneOdZera (n : SierpNat) : 0∸n = 0 := by
    induction n with
        | zero =>
            rfl
        | S n base =>
            have krok1 : 0∸n.S = P(0∸n) := by rfl
            rw [krok1]
            rw [base]
            rfl
theorem OdejmowanieOgraniczoneOdMniejszej (n m: SierpNat) : n∸(n+m) = 0 := by
    induction n with
        | zero =>
            change 0 ∸ (0 + m) = 0
            rw [PlusZeroII]
            exact OdejmowanieOgraniczoneOdZera m
        | S n base =>
            rw [lemmaDodawaniaNast]
            rw [SkracanieNastepnikowPrzyOdejm]
            exact base
theorem WlasnosciWiekszLiczb (n : SierpNat) : ∀m, n∸m = 0 → m = n + (m ∸ n) := by
    induction n with
        | zero =>
            intro m h1
            have krok1 : m∸SierpNat.zero = m := by rfl
            rw [krok1]
            change m = 0 + m
            rw [PlusZeroII]
        | S n base =>
            intro m h2
            cases m with
                | zero =>
                    change 0 = S n + 0∸S n
                    rw [OdejmowanieOgraniczoneOdZera]
                    rw [PlusZero]
                    change S n ∸ 0 = 0 at h2
                    have krok1 : S n ∸ 0 = S n := by rfl
                    rw [krok1] at h2
                    exact False.elim (A1 n h2)
                | S k =>
                    rw [SkracanieNastepnikowPrzyOdejm] at h2
                    rw [SkracanieNastepnikowPrzyOdejm]
                    rw [lemmaDodawaniaNast]
                    rw [←@base k h2]
theorem OdejmowanieOgraniczoneWlasnosciWieksz (n m : SierpNat) : n ∸ m = 0 ↔ ∃k, m = n + k := by
    apply Iff.intro
    ·intro h
     have krok1 : m = n + m∸n := WlasnosciWiekszLiczb n m h
     exists m∸n
    ·intro h
     cases h with
     | intro k row =>
        rw [row]
        exact OdejmowanieOgraniczoneOdMniejszej n k
theorem RownoscPrzezOdejmOgraniczone (n m :SierpNat) : n∸m = 0 ∧ m∸n=0 → n=m := by
    intro h
    have krok1 : m = n+(m∸n) := WlasnosciWiekszLiczb n m h.left
    rw [h.right] at krok1
    rw [PlusZero] at krok1
    rw [krok1]
theorem LiczbaWiekszLubMniejsz (n: SierpNat) :∀m : SierpNat, n∸m=0 ∨ m∸n=0 := by
    induction n  with
        | zero =>
            intro m
            exact Or.inl (OdejmowanieOgraniczoneOdZera m)
        | S n base =>
            intro m
            cases m with
                | zero =>
                    exact Or.inr (OdejmowanieOgraniczoneOdZera (S n))
                | S k =>
                    rw [SkracanieNastepnikowPrzyOdejm]
                    rw [SkracanieNastepnikowPrzyOdejm]
                    exact base k
theorem RozneOdZeraPrzezOdejmOgr (n m: SierpNat) : m∸n≠0 → m≠0 := by
    intro h
    intro hm
    rw [hm] at h
    exact h (OdejmowanieOgraniczoneOdZera n)
theorem AlternatywaOdejmowaniaOgraniczonego2Liczb (n : SierpNat) : ∀m:SierpNat, n∸m=0 ∨ m∸n=0 := by
    induction n with
        | zero =>
            intro m
            exact Or.inl (OdejmowanieOgraniczoneOdZera m)
        | S n base =>
            intro m
            apply Classical.byContradiction
            rw [PrawMorgana1]
            intro g
            have krok1 : ∃m1:SierpNat, m = S m1 := Twierdzenie2 m (RozneOdZeraPrzezOdejmOgr (S n) (m) g.right)
            have ⟨m1, row⟩ := krok1
            rw [row] at g
            rw [←PrawMorgana1] at g
            rw [SkracanieNastepnikowPrzyOdejm] at g
            rw [SkracanieNastepnikowPrzyOdejm] at g
            exact g (base m1)
theorem PrzechodnioscOdejmowaniaOgraniczonego (n : SierpNat) : ∀(m k : SierpNat), n∸m=0 ∧ m∸k=0 →
n∸k = 0 := by
    intro m k h
    have krok1 :∃g:SierpNat, k = m + g := (OdejmowanieOgraniczoneWlasnosciWieksz m k).mp h.right
    have ⟨g, hg⟩ := krok1
    have krok2 : ∃g2:SierpNat, m = n+g2 := (OdejmowanieOgraniczoneWlasnosciWieksz n m).mp h.left
    have ⟨g2, hg2⟩ := krok2
    rw [hg, hg2, ←LacznoscDodawania]
    exact OdejmowanieOgraniczoneOdMniejszej n (g2+g)
@[simp] def NierownoscSlaba (n m : SierpNat) := n∸m = 0
infixl:50 (priority := high) "≤" => NierownoscSlaba
theorem OdejmowanieOgraniczoneJednosci : ∀n:SierpNat, n∸1 = P n := by
    intro n
    have krok1 : n∸1 = P(n∸0) := by rfl
    rw [krok1]
    rfl
@[simp] def NierownoscOstra (n m : SierpNat) := n∸m=0 ∧ n≠m
infixl:50 (priority := high) "<" => NierownoscOstra
theorem WlasnosciNierownosciSlabejI (n : SierpNat) : 0 ≤ n := by
    simp
    exact OdejmowanieOgraniczoneOdZera n
theorem WlasnosciNierownosciSlabejZwrotnosc (n : SierpNat) : n≤n := by
    simp
    exact OdejmowanieOgraniczoneTychSamych n
theorem WlasnosciNierownosciSlabejPrzechodniosc (n m k : SierpNat) : n≤m ∧ m≤k → n≤k := by
    intro h
    simp
    simp at h
    exact PrzechodnioscOdejmowaniaOgraniczonego n m k h
#eval Δ (S (S (S (S zero))))
theorem WlasnosciNierownosciSlabejSpojnosc (n m : SierpNat) : n≤m ∨ m≤n := by
    simp
    exact AlternatywaOdejmowaniaOgraniczonego2Liczb n m
theorem WlasnosciNierownosciSlabejII (n m : SierpNat) : n≤m ↔ ∃k:SierpNat, m = n + k := by
    simp
    exact OdejmowanieOgraniczoneWlasnosciWieksz n m
theorem WlasnosciNierownosciOstraPrzeciwZwrotnosci (n : SierpNat) : ¬n<n := by
    simp
theorem WlasnoscNierownosciOstrej (n m : SierpNat) : n<m → ¬m<n := by
    intro h hm
    rw [NierownoscOstra] at h
    rw [NierownoscOstra] at hm
    have krok1 : n=m := RownoscPrzezOdejmOgraniczone n m (And.intro h.left hm.left)
    exact h.right krok1
theorem WlasnosciNierownosciOstrejPrzechodniosc (n m k : SierpNat) : n<m ∧ m<k → n<k := by
    intro h
    simp at h
    simp
    have ⟨h1,h2⟩ := h
    have krok1 : n∸k =0 := WlasnosciNierownosciSlabejPrzechodniosc n m k (And.intro h1.left h2.left)
    have krok2 : ¬n=k := by
        intro j
        have krok5 : m∸k=0 := h2.left
        rw [←j] at krok5
        exact h1.right (RownoscPrzezOdejmOgraniczone n m (And.intro h1.left krok5))
    exact And.intro krok1 krok2
theorem TrichotomiaNierownSlaba : ∀(n m : SierpNat), n<m ∧ ¬m<n ∧ ¬n=m ∨
m<n ∧ ¬n<m ∧ ¬m=n ∨
m=n ∧ ¬n<m ∧ ¬m<n := by
    intro n m
    by_cases h: m=n
    · have krok1 : ¬n<m := by
        apply Classical.byContradiction
        intro hn
        rw [←PrawaL.PrawPodwojnegoPrzeczenia] at hn
        rw [NierownoscOstra] at hn
        rw [eq_comm] at h
        exact (hn.right h)
      have krok7 : ¬m<n := by
        apply Classical.byContradiction
        intro hm
        rw [←PrawaL.PrawPodwojnegoPrzeczenia] at hm
        rw [NierownoscOstra] at hm
        exact hm.right h
      exact Or.inr (Or.inr (And.intro h (And.intro krok1 krok7)))
    · by_cases hw:n<m
      rw [eq_comm] at h
      · have krok2 : ¬m<n := WlasnoscNierownosciOstrej n m hw
        exact Or.inl (And.intro hw (And.intro krok2 h))
      · rw [NierownoscOstra] at hw
        rw [PrawaL.PrawMorgana2] at hw
        rw [ne_eq] at hw
        rw [←PrawaL.PrawPodwojnegoPrzeczenia] at hw
        rw [PrawaL.PrzemiennoscAlternatywy] at hw
        rw [eq_comm] at hw
        have krok2 : ¬m=n ∧ (m=n ∨ ¬n∸m=0) := And.intro h hw
        have krok1 : ¬n∸m=0 := (@PrawaL.PrawWnioskowaniaZAlternatyw (m=n) (¬n∸m=0)) krok2
        rw [PrawaL.PrzemiennoscAlternatywy] at hw
        rw [@PrawaL.PrawPodwojnegoPrzeczenia (m=n)] at hw
        rw [←PrawaL.PrawMorgana2] at hw
        have krok3 : m<n := by
            rw [NierownoscOstra]
            have step : m∸n=0 := PrawaL.PrawWnioskowaniaZAlternatyw (n∸m=0) (m∸n=0) (And.intro krok1 (WlasnosciNierownosciSlabejSpojnosc n m))
            exact And.intro step h
        have krok4 : ¬n<m := by
            rw [NierownoscOstra, ne_eq]
            have krok5 : ¬n=m ≡ ¬m=n := by
                rw [eq_comm]
            rw [krok5]
            exact hw
        exact Or.inr (Or.inl (And.intro krok3 (And.intro krok4 h)))
theorem WlasnoscRownosciOstrejZSlaba : ∀(n m : SierpNat), n≤m ⊻ m<n := by
    intro n m
    rw [AlternatywaWykluczajaca]
    have krok1 : n≤m ∨ m≤n := WlasnosciNierownosciSlabejSpojnosc n m
    cases krok1 with
        | inl h =>
            by_cases heq: n=m
            · have krok2 : ¬m<n := by
                intro k
                rw [NierownoscOstra] at k
                rw [eq_comm] at heq
                exact (k.right heq)
              exact Or.inl (And.intro h krok2)
            · have krok3 : ¬m≤n := by
                intro k
                have state1  : n=m := RownoscPrzezOdejmOgraniczone n m (And.intro h k)
                exact heq state1
              have krok4 : ¬m<n := by
                rw [NierownoscOstra, PrawaL.PrawMorgana2]
                rw [NierownoscSlaba] at krok3
                exact Or.inl krok3
              exact Or.inl (And.intro h krok4)
        | inr hp =>
            by_cases heq : m=n
            · have krok2 : n≤m := by
                rw [heq]
                rw [NierownoscSlaba]
                exact OdejmowanieOgraniczoneTychSamych n
              have krok3 : ¬m<n := by
                intro hn
                rw [NierownoscOstra] at hn
                exact hn.right heq
              exact Or.inl (And.intro krok2 krok3)
            · have krok1: m<n := by
                rw [NierownoscOstra]
                rw [NierownoscSlaba] at hp
                exact And.intro hp heq
              have krok2 : ¬n≤m := by
                intro k
                exact heq (RownoscPrzezOdejmOgraniczone m n (And.intro hp k))
              exact Or.inr (And.intro krok1 krok2)
theorem PrawaMorgDlaKwantSzczeg {α : Type u} (Φ : α → Prop) : (¬∀x,Φ x) ≡ ∃x,¬Φ x := by
  simp
theorem PrawaMorgDlaKwantEgzys {α : Type u} (Φ : α → Prop) : (¬∃x, Φ x) ≡ ∀x, ¬Φ x := by
  simp
theorem TTN : ∀(n m :SierpNat), n≤m ⊻ m<n := by
    intro n m
    have krok1 := TrichotomiaNierownSlaba n m
    rw [AlternatywaWykluczajaca]
    cases krok1 with
        | inl hL =>
            have ⟨k1,k2,k3⟩ := hL
            have k4 := k2
            rw [NierownoscSlaba]
            rw [NierownoscOstra] at k2
            rw [PrawaL.PrawMorgana2] at k2
            rw [eq_comm] at k3
            rw [ne_eq] at k2
            rw [←PrawaL.PrawPodwojnegoPrzeczenia] at k2
            rw [PrawaL.PrzemiennoscAlternatywy] at k2
            have krok2 := PrawaL.PrawWnioskowaniaZAlternatyw  (m=n) (¬m∸n=0) (And.intro k3 k2)
            exact Or.inl (And.intro k1.left k4)
        | inr hR =>
            cases hR with
                | inl hLL =>
                    have ⟨l1,l2,l3⟩ := hLL
                    have krok1 : ¬n≤m := by
                        intro h
                        rw [NierownoscSlaba] at h
                        rw [NierownoscOstra] at l1
                        exact l3 (RownoscPrzezOdejmOgraniczone m n (And.intro l1.left h))
                    exact Or.inr (And.intro l1 krok1)
                | inr hRR =>
                    have ⟨r1,r2,r3⟩ := hRR
                    have krok1 : n≤m := by
                        rw [NierownoscSlaba, r1]
                        exact OdejmowanieOgraniczoneTychSamych n
                    exact Or.inl (And.intro krok1 r3)
theorem KazdaLiczbaMniejszaOdNastepnika : ∀n:SierpNat, n < S n := by
    intro n
    rw [NierownoscOstra]
    have krok1 := Twierdzenie1 n
    rw [NastepnikPrzezSume]
    have krok2 := OdejmowanieOgraniczoneOdMniejszej n (S 0)
    exact And.intro krok2 krok1
theorem NieistniejeLiczbaMiedzyNastepnikPoprz : ∀n:SierpNat, ¬(∃m:SierpNat, n<m ∧ m<S n) := by
    intro n
    rw [PrawaMorgDlaKwantEgzys]
    intro m
    intro g
    have ⟨k1,k2⟩ := g
    rw [NierownoscOstra] at k1
    rw [NierownoscOstra] at k2
    have ⟨g1,g2⟩ := k1
    have ⟨g3,g4⟩ := k2
    have krok1 := (OdejmowanieOgraniczoneWlasnosciWieksz m (S n)).mp g3
    have krok2 := (OdejmowanieOgraniczoneWlasnosciWieksz n m).mp g1
    rw [NastepnikPrzezSume] at krok1
    have ⟨x,hx⟩ := krok1
    have ⟨y,hy⟩ := krok2
    have krok6 : x≠0 := by
        intro k
        rw [k, ←NastepnikPrzezSume, PlusZero, eq_comm] at hx
        exact g4 hx
    rw [hy] at hx
    have krok3 : y ≠ 0 := by
        intro k
        rw [k] at hy
        rw [PlusZero, eq_comm] at hy
        exact g2 hy
    have krok4 := Twierdzenie2 y krok3
    have ⟨l1,kl⟩ := krok4
    rw [kl,←LacznoscDodawania, lemmaDodawaniaNast, ZamianaNastepnika, ZamianaNastepnika] at hx
    rw [lemmaDodawaniaNast, lemmaDodawaniaNast, PlusZero] at hx
    have krok5 := A2 n (n+(l1+x)) hx
    have krok7 := Twierdzenie2 x krok6
    have ⟨l2,hl2⟩ := krok7
    rw [hl2, ZamianaNastepnika, LacznoscDodawania, ←LacznoscDodawania, eq_comm] at krok5
    have krok8 := PrawoWnioskowaniaZera n (S l1 + l2) krok5
    rw [lemmaDodawaniaNast] at krok8
    exact A1 (l1+l2) krok8
theorem Dyskretyzacja : ∀(n m : SierpNat), n<m → S n ≤ m := by
    intro n m hnm
    rw [NierownoscSlaba]
    rw [NierownoscOstra] at hnm
    have krok1 := (OdejmowanieOgraniczoneWlasnosciWieksz n m).mp hnm.left
    have ⟨x,hx⟩ := krok1
    have krok2 : x≠0 := by
        intro h
        rw [h, PlusZero, eq_comm] at hx
        exact hnm.right hx
    have krok3 := Twierdzenie2 x krok2
    have ⟨l, hl⟩ := krok3
    rw [hl, ZamianaNastepnika] at hx
    have krok4 : ∃l:SierpNat, m = S n + l := Exists.intro l hx
    have krok5 := (OdejmowanieOgraniczoneWlasnosciWieksz (S n) m).mpr krok4
    exact krok5
theorem NieistniejeLiczbaMiedzyNastepnikPoprzII : ∀n:SierpNat, ¬(∃m:SierpNat, n<m ∧ m<S n) := by
    intro n h
    have ⟨m, hm⟩ := h
    have krok1 := Dyskretyzacja n m hm.left
    have ⟨h1,h2⟩ := hm
    have krok2 := RownoscPrzezOdejmOgraniczone m (S n) (And.intro h2.left krok1)
    exact h2.right krok2
theorem KuratZad1 {e : Prop} : ((p → q) ∧ (r → e)) → (((p∧r) → q∧e) ∧ ((p∨r) → (q∨e))) := by
    intro h
    constructor
    · intro k
      exact And.intro (h.left k.left) (h.right k.right)
    · intro k
      cases k with
        | inl hp =>
            exact Or.inl (h.left hp)
        | inr hr =>
            exact Or.inr (h.right hr)
theorem KuratZad2 : (p → q) → ((p∧q≡p) ∧ (p∨q≡q)) := by
    intro h
    constructor
    · constructor
      · intro hk
        exact hk.left
      · intro hp
        exact And.intro hp (h hp)
    · constructor
      · intro ha
        cases ha with
            | inl hp =>
              exact h hp
            | inr hq =>
                exact hq
      · intro hq
        exact Or.inr hq
theorem KuratZad3 : p∨p≡p := by
    apply Iff.intro
    intro h
    cases h with
    |inl hp =>
        exact hp
    | inr hp =>
        exact hp
    intro hp
    exact Or.inl hp
theorem KuratZad3b : p ≡ p∧p := Iff.intro
(fun hp:p => And.intro hp hp)
(fun h:p∧p => h.left)
theorem PrawoAbsorbcjiI : p∨(p∧q) ≡ p := by
    apply Iff.intro
    · intro h
      cases h with
        | inl hp =>
            exact hp
        | inr hk =>
            exact hk.left
    · intro hp
      exact Or.inl hp
theorem PrawoAbsorbcjiII : p ≡ p∧(p∨q) := by
    apply Iff.intro
    · intro hp
      exact And.intro (hp) (Or.inl hp)
    · intro hk
      exact hk.left
theorem test : p∧(q∨r) ≡ (p∧q)∨(p∧r) := PrawaL.PrawRozdzielnosciI
theorem test2 : p∨(q∧r) ≡ (p∨q)∧(p∨r) := by
    apply Iff.intro
    · intro h
      cases h with
        | inl hp =>
            exact And.intro (Or.inl hp) (Or.inl hp)
        | inr hk =>
            exact And.intro (Or.inr hk.left) (Or.inr hk.right)
    · intro hk
      cases hk.left with
        | inl hp =>
            exact Or.inl hp
        | inr hq =>
            cases hk.right with
                | inl hp =>
                    exact Or.inl hp
                | inr hr =>
                    exact Or.inr (And.intro hq hr)
theorem DodawanieDoNierownosciOstr : ∀(n m l k : SierpNat), (n < m) ∧ (l ≤ k) → n+l < m + k := by
    intro n m l k h
    have ⟨h1,h2⟩ := h
    rw [NierownoscOstra] at h1
    rw [NierownoscSlaba] at h2
    have krok1 := (OdejmowanieOgraniczoneWlasnosciWieksz n m).mp h1.left
    have ⟨k1,hm⟩ := krok1
    have krok2 := (OdejmowanieOgraniczoneWlasnosciWieksz l k).mp h2
    have ⟨g, hg⟩ := krok2
    have krok3 : k1≠0 := by
        intro hk
        rw [hk, PlusZero, eq_comm] at hm
        exact h1.right hm
    have krok4 : m + k = (n + l) + (g + k1) := by
        calc
            m + k = (n+k1) + (l+g) := by rw [←hg, ←hm]
            _ = n +(k1 + (l + g)) := by rw [←LacznoscDodawania]
            _ = n+((l+g) + k1) := by rw [PrzemiennoscDodawania k1]
            _ = (n + (l+g))+k1 := by rw [LacznoscDodawania]
            _ = ((n+l)+g)+k1 := by rw [LacznoscDodawania]
            _ = (n+l) + (g+k1) := by rw [LacznoscDodawania]
    have krok5 : g+k1≠0 := by
        intro f
        have step1 : k1 = 0 := by
            cases k1 with
                | zero =>
                    rfl
                | S j =>
                    rw [ZamianaNastepnika, lemmaDodawaniaNast] at f
                    exact False.elim (A1 (g+j) f)
        exact krok3 step1
    have krok6 : m+k≠n+l := by
        intro f
        rw [f] at krok4
        have step1 : g+k1 = 0 := by
            rw [eq_comm] at krok4
            exact (PrawoWnioskowaniaZera (n+l) (g+k1)) krok4
        exact krok5 step1
    have krok7 : (n+l)∸(m+k) = 0 := (OdejmowanieOgraniczoneWlasnosciWieksz (n+l) (m+k)).mpr (Exists.intro (g+k1) krok4)
    rw [NierownoscOstra]
    rw [ne_eq, eq_comm] at krok6
    exact And.intro krok7 krok6
theorem NastepnikPoprzednika : ∀n:SierpNat, n≠0 → S (P n) = n := by
    intro n h
    induction n with
        | zero =>
            change 0≠0 at h
            have krok1 := Eq.refl SierpNat.zero
            exact False.elim (h krok1)
        | S k base =>
            rfl
theorem lemmaNierownoscPoprzednikI : ∀(n m : SierpNat), S n = m → n = m∸1 := by
    intro n m
    intro h
    rw [←h]
    rfl
theorem MnozeniePrzezZeroII (n : SierpNat): n*0 = 0 := by
    rw [PrzemiennoscMnozenia, MnozeniePrzezZero]
theorem NierownosciOstr : ∀(n m l: SierpNat), n < m → n+l<m+l := by
    intro n m l
    intro  h
    have krok1 := OdejmowanieOgraniczoneTychSamych l
    rw [←NierownoscSlaba] at krok1
    exact DodawanieDoNierownosciOstr n m l l (And.intro h krok1)
theorem lemmaNierown : ∀(n m l : SierpNat), n<m ∧ m≤l → n<l := by
    intro n m l h
    have krok1 := PrzechodnioscOdejmowaniaOgraniczonego n m l (And.intro h.left.left h.right)
    have krok2 : n≠l := by
        intro k
        have ⟨h1,h2⟩ := h
        rw [←k] at h2
        have step1 := RownoscPrzezOdejmOgraniczone n m (And.intro h.left.left h2)
        exact h.left.right step1
    exact And.intro krok1 krok2
theorem lemmaOdejmowanOgran : ∀(n m l : SierpNat), (n+l)∸(m+l) = 0 → n∸m=0 := by
    intro n m l h
    induction l with
        | zero =>
            change (n+0)∸(m+0)=0 at h
            rw [PlusZero, PlusZero] at h
            exact h
        | S l base =>
            rw [ZamianaNastepnika, lemmaDodawaniaNast, ZamianaNastepnika, lemmaDodawaniaNast] at h
            rw [SkracanieNastepnikowPrzyOdejm] at h
            exact base h
theorem NierownosciOstrII : ∀(n m l : SierpNat), n+l<m+l → n<m := by
    intro n m l h
    have krok3 := lemmaOdejmowanOgran n m l h.left
    have krok4 : n≠m := by
        intro k
        rw [←k] at h
        exact WlasnosciNierownosciOstraPrzeciwZwrotnosci (n+l) h
    exact And.intro krok3 krok4
theorem NierownosciOstrIII : ∀(n m l: SierpNat), n≤m → n+l≤m+l := by
    intro n m l h
    apply Classical.byContradiction
    intro k
    have krok1 := PrawaL.PrawWnioskowaniaZAlternatyw (n+l≤m+l) (m+l≤n+l)
        (And.intro k (WlasnosciNierownosciSlabejSpojnosc (n+l) (m+l)))
    have krok2 := lemmaOdejmowanOgran m n l krok1
    have krok3 := RownoscPrzezOdejmOgraniczone n m (And.intro h krok2)
    rw [krok3] at k
    have krok4 : m+l≤m+l := OdejmowanieOgraniczoneTychSamych (m+l)
    exact k krok4
theorem PrawSkracaniaRow : ∀(n m l: SierpNat), n+l = m+l → n=m := by
    intro n m l h
    induction l with
        | zero =>
            change n+0=m+0 at h
            rw [PlusZero] at h
            exact h
        | S k base =>
            rw [ZamianaNastepnika, ZamianaNastepnika, lemmaDodawaniaNast, lemmaDodawaniaNast] at h
            exact base (A2 (n+k) (m+k) h)
theorem NierownSlabaZOstr : ∀(n m : SierpNat), n<m → n≤m := by
    intro n m h
    exact h.left
theorem DodawanieNierwnosciSlab : ∀(n m l k : SierpNat), n≤m ∧ l≤k → n+l≤m+k := by
    intro n m l k h
    have krok1 := NierownosciOstrIII n m l h.left
    have krok2 := NierownosciOstrIII l k m h.right
    rw [PrzemiennoscDodawania, PrzemiennoscDodawania k m] at krok2
    exact WlasnosciNierownosciSlabejPrzechodniosc (n+l) (m+l) (m+k) (And.intro krok1 krok2)
theorem lemmaMnozenieNierownPraw : ∀(n m l : SierpNat), n≤m → n*l≤m*l := by
    intro n m l h
    induction l with
    | zero =>
        change n*0=m*0
        rfl
    | S l base =>
        rw [PrawMnozenia,PrawMnozenia]
        exact DodawanieNierwnosciSlab (n*l) (m*l) n m (And.intro base h)
theorem MnozenieNierowI : ∀ (n m l k : SierpNat), n<m ∧ l≤k → n*l ≤ m*k := by
    intro n m l k hk
    have krok1 := hk.left.left
    rw [←NierownoscSlaba] at krok1
    have krok2 := lemmaMnozenieNierownPraw n m l krok1
    have krok3 := lemmaMnozenieNierownPraw l k m hk.right
    rw [PrzemiennoscMnozenia, PrzemiennoscMnozenia k m] at krok3
    exact WlasnosciNierownosciSlabejPrzechodniosc (n*l) (m*l) (m*k) (And.intro krok2 krok3)
theorem lemmaMnozenieNierowOstr : ∀(n m l : SierpNat), n<m ∧ l≠0 → n*l<m*l := by
    intro n m l h
    have krok1 := NierownSlabaZOstr n m h.left
    have krok3 := Twierdzenie2 l h.right
    have ⟨k1,hk1⟩ := krok3
    rw [hk1, PrawMnozenia, PrawMnozenia]
    have krok4 := NierownosciOstr n m (n*k1) h.left
    have krok5 := WlasnosciNierownosciSlabejZwrotnosc m
    have krok2 := lemmaMnozenieNierownPraw n m k1 krok1
    have krok7 := NierownosciOstrIII (n*k1) (m*k1) m krok2
    rw [PrzemiennoscDodawania, PrzemiennoscDodawania (m*k1)] at krok7
    have krok8 := lemmaNierown (n+n*k1) (m+n*k1) (m+m*k1) (And.intro krok4 krok7)
    rw [PrzemiennoscDodawania, PrzemiennoscDodawania m] at krok8
    exact krok8
theorem lemmaNierownII : ∀(n m k), n≤m ∧ m<k → n<k := by
    intro n m k h
    have krok1 := PrzechodnioscOdejmowaniaOgraniczonego n m k (And.intro h.left h.right.left)
    have krok2 : n≠k := by
        intro h2
        rw [h2] at h
        have step := RownoscPrzezOdejmOgraniczone m k (And.intro h.right.left h.left)
        exact h.right.right step
    exact (And.intro krok1 krok2)
theorem MnozenieNierowII : ∀ (n m l k : SierpNat), n<m ∧ l≤k ∧ k≠0 → n*l < m*k := by
    intro n m l k h
    have ⟨h1,h2,h3⟩ := h
    have krok1 := (lemmaMnozenieNierowOstr n m k (And.intro h1 h3))
    have krok3 := lemmaMnozenieNierownPraw l k n h.right.left
    rw [PrzemiennoscMnozenia, @PrzemiennoscMnozenia k n] at krok3
    exact lemmaNierownII (n*l) (n*k) (m*k) (And.intro krok3 krok1)
theorem lemmaNegNierwonosciSlab : ∀(n m : SierpNat), ¬n≤m → m<n := by
    intro n m h
    have krok1 := PrawaL.PrawWnioskowaniaZAlternatyw (n≤m) (m≤n) (And.intro h (WlasnosciNierownosciSlabejSpojnosc n m))
    have krok2 : m≠n := by
        intro h2
        have krok3 : n≤m := by
            rw [h2]
            exact OdejmowanieOgraniczoneTychSamych n
        exact h krok3
    exact (And.intro krok1 krok2)
theorem SkracanieNierownosciSlabej : ∀(n m l : SierpNat), n*l≤m*l ∧ l≠0 → n≤m := by
    intro n m l h
    apply Classical.byContradiction
    intro h2
    have krok1 := lemmaNegNierwonosciSlab n m h2
    have krok2 := lemmaMnozenieNierowOstr m n l (And.intro krok1 h.right)
    have krok3 := RownoscPrzezOdejmOgraniczone (m*l) (n*l) (And.intro krok2.left h.left)
    exact krok2.right krok3
theorem SkracanieMnozen (n m l : SierpNat) : n*l = m*l ∧ l≠0 → n=m := by
    intro h
    have krok1 : n*l≤m*l := by
        rw [h.left]
        exact WlasnosciNierownosciSlabejZwrotnosc (m*l)
    have krok2 : m*l≤n*l := by
        rw [h.left]
        exact WlasnosciNierownosciSlabejZwrotnosc (m*l)
    have krok3 := SkracanieNierownosciSlabej n m l (And.intro krok1 h.right)
    have krok4 := SkracanieNierownosciSlabej m n l (And.intro krok2 h.right)
    exact RownoscPrzezOdejmOgraniczone n m (And.intro krok3 krok4)
theorem lemmaNierowOstrNaNast : ∀(n m : SierpNat), n<m → (S n ≤ m) := by
    intro n m h
    apply Classical.byContradiction
    intro hn
    have step1 := lemmaNegNierwonosciSlab (S n) m hn
    have step2 := (WlasnosciNierownosciSlabejII n m).mp (h.left)
    exact NieistniejeLiczbaMiedzyNastepnikPoprz n (Exists.intro m (And.intro h step1))
theorem NegacjaKwantGlow {α : Type u} (Φ : α → Prop) : ¬(∀x,Φ x) ≡ ∃x,¬Φ x := by
    rw [←Classical.not_exists_not]
    rw [←PrawaL.PrawPodwojnegoPrzeczenia]
theorem PrawaMorgDlaKwantEgzysII {α : Type u} (Φ : α → Prop) : (¬∃x,¬Φ x) ≡ ∀x, Φ x := by
  simp
def ZbiorOgraniczony (A : Set SierpNat):Prop := ∃(m:SierpNat),∀(n:SierpNat),n∈A → n<m
structure ZbiorOgraniczonyNiePustyNat where
    zbior : Set SierpNat
    ogr : ZbiorOgraniczony zbior
    ist : ∃(m:SierpNat), m∈zbior
axiom Indukcjaa {A : Set SierpNat} : (SierpNat.zero ∈ A ∧ (∀n:SierpNat,n∈A → (S n ∈A))) → ∀(m:SierpNat),m∈A
theorem KazdaLiczbaMniejszaRownOdZera : ∀(n:SierpNat), (0 ≤ n) := by
    intro n
    have krok1 : n=0 ∨ (∃(m:SierpNat), n = S m) := by
        by_cases h : n=0
        exact Or.inl h
        have krok1 := Twierdzenie2 n h
        exact Or.inr krok1
    cases krok1 with
        | inl hl =>
            rw [hl]
            rfl
        | inr hr =>
            have ⟨m, hm⟩ := hr
            exact OdejmowanieOgraniczoneOdZera n
theorem ZasadaMaksimum : ∀(A : ZbiorOgraniczonyNiePustyNat),∃(max:SierpNat),max∈A.zbior ∧ (∀k:SierpNat,k∈A.zbior → k≤max) := by
    intro A
    apply Classical.byContradiction
    intro h
    rw [PrawaMorgDlaKwantEgzys] at h
    have krok1 := A.ist
    have ⟨m, hm⟩ := krok1
    have krok2 := h m
    rw [PrawaL.PrawMorgana2,PrawaMorgDlaKwantSzczeg] at krok2
    cases krok2 with
        | inl hl =>
            exact hl hm
        | inr hr =>
            have ⟨x, hx⟩ := hr
            rw [PrawaL.ImpPrzezAlt, PrawaL.PrawMorgana1,←PrawaL.PrawPodwojnegoPrzeczenia] at hx
            have krok3 := lemmaNegNierwonosciSlab x m hx.right
            have krok4 := KazdaLiczbaMniejszaRownOdZera m
            let Z0 : Set SierpNat := fun (x:SierpNat) =>∃g, (g∈A.zbior) ∧ x ≤ g
            have krok5 := KazdaLiczbaMniejszaRownOdZera m
            have krok6 : SierpNat.zero ∈ Z0 :=(Exists.intro m (And.intro hm krok5))
            have krok7 : ∀(n:SierpNat),n∈Z0 → (S n ∈Z0) := by
                intro n hn
                have ⟨g,hg⟩ := hn
                have step2 := h g
                rw [PrawaL.PrawMorgana2] at step2
                cases step2 with
                    | inl hl2 =>
                        exact False.elim (hl2 hg.left)
                    | inr hr2 =>
                        rw [PrawaMorgDlaKwantSzczeg] at hr2
                        have ⟨x2,hx2⟩ := hr2
                        rw [PrawaL.ImpPrzezAlt, PrawaL.PrawMorgana1,←PrawaL.PrawPodwojnegoPrzeczenia] at hx2
                        have step3 := lemmaNegNierwonosciSlab x2 g hx2.right
                        have step4 := lemmaNierownII n g x2 (And.intro hg.right step3)
                        have step5 := lemmaNierowOstrNaNast n x2 step4
                        have step6 :(S n)∈ Z0 := (Exists.intro x2 (And.intro hx2.left step5))
                        exact step6
            have krok8 := Indukcjaa (And.intro krok6 krok7)
            have krok9 := A.ogr
            rw [ZbiorOgraniczony] at krok9
            have ⟨l0, hl0⟩ := krok9
            have krok10 := krok8 l0
            have ⟨w,hw⟩ := krok10
            have krok11 := hl0 w hw.left
            exact (krok11.right (RownoscPrzezOdejmOgraniczone w l0 (And.intro krok11.left hw.right)))
theorem ZasadaMinimum (A : Set SierpNat) (h : ∃m:SierpNat,m∈A) : ∃k:SierpNat,k∈A ∧ (∀n:SierpNat, n∈A → k≤n) := by
    have ⟨m, hm⟩ := h
    by_cases hz : m = 0
    have krok1 : ∀a:SierpNat,a∈A → m≤a := by
        intro a ha
        rw [hz]
        exact OdejmowanieOgraniczoneOdZera a
    exact Exists.intro m (And.intro hm krok1)
    let Z0 : Set SierpNat := fun g:SierpNat => ∀n:SierpNat,n∈A → g<n
    apply Classical.byContradiction
    rw [PrawaMorgDlaKwantEgzys]
    intro hx
    have krok1 := hx m
    rw [PrawaL.PrawMorgana2, PrawaMorgDlaKwantSzczeg] at krok1
    cases krok1 with
        | inl hl =>
            exact hl hm
        | inr hr =>
            have ⟨x, h2⟩ := hr
            rw [PrawaL.ImpPrzezAlt, PrawaL.PrawMorgana1, ←PrawaL.PrawPodwojnegoPrzeczenia] at h2
            have step1 := lemmaNegNierwonosciSlab m x h2.right
            have ogrZ0 : ZbiorOgraniczony Z0 := by
                rw [ZbiorOgraniczony]
                apply Classical.byContradiction
                rw [PrawaMorgDlaKwantEgzys]
                intro s
                have step2 := s m
                rw [PrawaMorgDlaKwantSzczeg] at step2
                have ⟨x2, hx2⟩ := step2
                rw [PrawaL.ImpPrzezAlt, PrawaL.PrawMorgana1,←PrawaL.PrawPodwojnegoPrzeczenia] at hx2
                have ⟨k1, k2⟩ := hx2
                have step3 := k1 m hm
                exact hx2.right step3
            have istZ0 : ∃(f:SierpNat),f∈Z0 := by
                have step2 : 0∈Z0 := by
                    apply Classical.byContradiction
                    intro hh
                    have s1 := hx 0
                    rw [PrawaL.PrawMorgana2, PrawaMorgDlaKwantSzczeg] at s1
                    cases s1 with
                        | inl hl =>
                            change ¬(∀n:SierpNat,(n∈A → 0<n)) at hh
                            rw [PrawaMorgDlaKwantSzczeg] at hh
                            have ⟨k, hk⟩ := hh
                            rw [PrawaL.ImpPrzezAlt, PrawaL.PrawMorgana1,←PrawaL.PrawPodwojnegoPrzeczenia] at hk
                            have krok1 := hk.right
                            rw [NierownoscOstra, PrawaL.PrawMorgana2, ne_eq, ←PrawaL.PrawPodwojnegoPrzeczenia] at krok1

                            have krok2 : 0∈A := by
                                cases krok1 with
                                    | inl hl2 =>
                                        rw [←ne_eq] at hl2
                                        exact False.elim ((RozneOdZeraPrzezOdejmOgr k 0 hl2) (Eq.refl 0))
                                    | inr hr2 =>
                                        rw [hr2]
                                        exact hk.left
                            exact hl krok2
                        | inr hr2 =>
                            have ⟨k, hk⟩ := hr2
                            rw [PrawaL.ImpPrzezAlt, PrawaL.PrawMorgana1,←PrawaL.PrawPodwojnegoPrzeczenia] at hk
                            have krok1 := lemmaNegNierwonosciSlab 0 k hk.right
                            have krok2 := lemmaNierowOstrNaNast k 0 krok1
                            have krok3 := OdejmowanieOgraniczoneOdZera (S k)
                            have krok4 := RownoscPrzezOdejmOgraniczone 0 (S k) (And.intro krok3 krok2)
                            rw [eq_comm] at krok4
                            exact A1 k krok4
                exact Exists.intro 0 step2
            let Z0_structer : ZbiorOgraniczonyNiePustyNat := {
                zbior := Z0
                ogr := ogrZ0
                ist := istZ0
            }
            have krok1 := ZasadaMaksimum Z0_structer
            have ⟨max, hmax⟩ := krok1
            have krok2 : (S max)∈A := by
                have step2 : max < S max := by
                    have s1 : max ∸ S max = 0 := by
                        rw [OdejmowanieOgraniczone, OdejmowanieOgraniczoneTychSamych]
                        rfl
                    exact And.intro s1 (Twierdzenie1 max)
                have ⟨f, hf⟩ := istZ0
                have krok3 : max∈Z0 := hmax.left
                apply Classical.byContradiction
                intro hnm
                have step3 : (S max)∈Z0 := by
                    intro n hn
                    have step4 : max < n := krok3 n hn
                    have step5 : (S max)≤n := lemmaNierowOstrNaNast max n step4
                    by_cases l : (S max) = n
                    rw [←l] at hn
                    exact False.elim (hnm hn)
                    exact (And.intro step5 l)
                have krok4 := hmax.right (S max) step3
                have krok41 : max∸(S max) = 0 := by
                    rw [OdejmowanieOgraniczone, OdejmowanieOgraniczoneTychSamych max]
                    rfl
                have krok5 := RownoscPrzezOdejmOgraniczone (max) (S max) (And.intro krok41 krok4)
                exact ((Twierdzenie1 max) krok5)
            have krok3 := hx (S max)
            rw [PrawaL.PrawMorgana2] at krok3
            cases krok3 with
                | inl hl =>
                    exact hl krok2
                | inr hr2 =>
                    rw [PrawaMorgDlaKwantSzczeg] at hr2
                    have ⟨max2, hmax2⟩ := hr2
                    rw [PrawaL.ImpPrzezAlt, PrawaL.PrawMorgana1, ←PrawaL.PrawPodwojnegoPrzeczenia] at hmax2
                    have step11 := lemmaNegNierwonosciSlab (S max) (max2) hmax2.right
                    have step2 : max<max2 := hmax.left max2 hmax2.left
                    have step31 := lemmaNierowOstrNaNast (max) (max2) step2
                    have step3 := RownoscPrzezOdejmOgraniczone (S max) (max2) (And.intro step31 step11.left)
                    exact hmax2.right step31
@[simp] def Potegowanie (n m :SierpNat) :=
    match m with
        | SierpNat.zero => 1
        | SierpNat.S k => (Potegowanie n k) * n
notation:90 (priority := high) n"^"m => Potegowanie n m
theorem DoPierwszejPotegi : ∀n, (n^1) = n := by
    intro n
    have step1 : (n^0) = 1 := by rfl
    calc
        (n^1) = (n^0) * n := by rfl
        _ = 1 * n := by rw [step1]
        _ = n := by rw [IstnienieJednosci]
theorem DodawanieWPotedze : ∀(n m k : SierpNat), (n^(m+k)) = (n^m) * (n^k) := by
    intro n m k
    induction k with
        | zero =>
            simp
            rw [PrzemiennoscMnozenia, IstnienieJednosci]
            change (n^(m+0)) = (n^m)
            rw [PlusZero]
        | S k base =>
            change (n^(m+ (S k))) = (n^m)*(n^k.S)
            rw [NastepnikPrzezSume k, LacznoscDodawania]
            rw [←NastepnikPrzezSume]
            have step1 : (n^(S (m+k))) = (n^(m+k))*n := by
                rfl
            rw [step1, base, ←LacznoscMnozenia2]
            have step2 : (n^k)*n = (n^(S k)) := by rfl
            rw [step2]
theorem PotegaPotegi : ∀(n m k : SierpNat), ((n^m)^k) = (n^(m*k)) := by
    intro n m k
    induction k with
        | zero =>
            rfl
        | S k base =>
            change ((n^m)^(S k)) = (n^(m*(S k)))
            rw [NastepnikPrzezSume, DodawanieWPotedze]
            have step1 : ((n^m)^(S 0)) = (n^m) := by
                simp
                have step1 : ((n^m)^0) = 1 := by rfl
                rw [step1, IstnienieJednosci]
            rw [step1, base,←DodawanieWPotedze, ←PrawMnozenia,NastepnikPrzezSume]
@[simp] def sgn (n :SierpNat) :=
    match n with
        | .zero => SierpNat.zero
        | SierpNat.S k => SierpNat.zero.S
@[simp] def reszta (n m :SierpNat) :=
    match n with
        | .zero => 0
        | SierpNat.S k => (S (reszta k m)) * (sgn (m ∸ (S (reszta k m))))
#eval reszta SierpNat.zero.S.S.S.S SierpNat.zero.S.S.S.S.S
@[simp] def Wynikdzielnienia (n m : SierpNat) :=
    match n with
        | .zero => 0
        | SierpNat.S k => (Wynikdzielnienia k m) + (1 ∸ (reszta (S k) m))
theorem OdejmowanieOgraniczoneWiekszOdZera : ∀(n m : SierpNat), n<m → 0<m∸n := by
    intro n m h
    apply Classical.byContradiction
    intro h2
    rw [NierownoscOstra, PrawaL.PrawMorgana2, ne_eq, ←PrawaL.PrawPodwojnegoPrzeczenia] at h2
    cases h2 with
        | inl hl =>
            exact hl (OdejmowanieOgraniczoneOdZera (m∸n))
        | inr hr =>
            have krok1 := RownoscPrzezOdejmOgraniczone n m (And.intro h.left (eq_comm.mp hr))
            exact h.right krok1
theorem sgmRowne1 : ∀(n m : SierpNat), 0<m∸n → sgn (m ∸ n) = 1 := by
    intro n m h
    have krok1 := h.right
    rw [ne_comm] at krok1
    have step1 := Twierdzenie2 (m∸n) (krok1)
    have ⟨g, hg⟩ := step1
    rw [hg]
    rfl
theorem WlasciwosciResztyI : ∀(n m : SierpNat), (0<m) → (reszta n m) < m := by
    intro n m hm
    induction n with
        | zero =>
            have step1 : reszta .zero m = 0 := by rfl
            rw [step1]
            exact hm
        | S k base =>
            have step1 := lemmaNierowOstrNaNast (reszta k m) m base
            by_cases h : (S (reszta k m)) ≠ m
            rw [NierownoscSlaba] at step1
            have krok1 := And.intro step1 h
            rw [←NierownoscOstra] at krok1
            change reszta (S k) m < m
            have krok2 : reszta (S k) m = (S (reszta k m)) * (sgn (m ∸ (S (reszta k m)))) := by
                rfl
            have krok3 : sgn (m ∸ (S (reszta k m))) = 1 := by
                have step2 := (WlasnosciNierownosciSlabejII (S (reszta k m)) m).mp krok1.left
                exact sgmRowne1 (S (reszta k m)) m (OdejmowanieOgraniczoneWiekszOdZera (S (reszta k m)) m krok1)
            rw [krok3, PrzemiennoscMnozenia, IstnienieJednosci] at krok2
            rw [krok2]
            exact krok1
            rw [ne_eq, ←PrawaL.PrawPodwojnegoPrzeczenia] at h
            have krok1 : reszta k.S m = 0 := by
                rw [reszta, h, (OdejmowanieOgraniczoneTychSamych m)]
                rfl
            rw [krok1]
            exact hm
theorem WlasnosciRozkladu : ∀(n m :SierpNat), (0<m) → n = m*(Wynikdzielnienia n m) + (reszta n m) := by
    intro n m hm
    induction n with
        | zero =>
            rfl
        | S k base =>
            rw [Wynikdzielnienia, reszta, RozdzielnoscMnozeniaL]
            have krok1 := WlasciwosciResztyI k m hm
            have krok2 := lemmaNierowOstrNaNast (reszta k m) m krok1
            by_cases h : S (reszta k m) = m
            rw [h, OdejmowanieOgraniczoneTychSamych m]
            have krok3 : sgn 0 = 0 := by rfl
            rw [krok3, MnozeniePrzezZeroII, PlusZero]
            have krok4 : 1∸0 = 1 := by rfl
            rw [krok4,PrzemiennoscMnozenia m 1, IstnienieJednosci]
            have krok5 : reszta k m = m∸1 := by
                exact lemmaNierownoscPoprzednikI (reszta k m) m h
            rw [krok5] at base
            have krok6 : m = m∸1 + 1 := by
                change m = m∸1 + S 0
                rw [←NastepnikPrzezSume, OdejmowanieOgraniczoneJednosci]
                have step1 := NastepnikPoprzednika m (ne_comm.mp hm.right)
                rw [step1]
            conv =>
                right
                conv =>
                    right
                    rw [krok6]
                rw [LacznoscDodawania, ←base]
            rfl
            have krok3 : (S (reszta k m)) < m := And.intro (krok2) h
            have krok4 := OdejmowanieOgraniczoneWiekszOdZera (S (reszta k m)) m krok3
            have krok5 := sgmRowne1 (S (reszta k m)) m krok4
            rw [krok5,PrzemiennoscMnozenia (S (reszta k m)), IstnienieJednosci]
            have krok6 : 1≤ (S (reszta k m)) := by
                have step1 := WlasnosciNierownosciSlabejI (reszta k m)
                have step2 := DodawanieNierwnosciSlab 0 (reszta k m) 1 1 (And.intro step1 (WlasnosciNierownosciSlabejZwrotnosc 1))
                change 0 + S 0 ≤ (reszta k m) + S 0 at step2
                rw [NastepnikPrzezSume]
                rw [←NastepnikPrzezSume] at step2
                exact step2
            by_cases h2 : 1 = S (reszta k m)
            rw [←h2, OdejmowanieOgraniczoneTychSamych 1, MnozeniePrzezZeroII,PlusZero]
            have step1 := eq_comm.mp h2
            have step2 := lemmaNierownoscPoprzednikI (reszta k m) 1 step1
            rw [OdejmowanieOgraniczoneTychSamych 1] at step2
            rw [step2, PlusZero] at base
            rw [←base]
            rfl
            have step1 : 1 < (S (reszta k m)) := And.intro krok6 h2
            rw [step1.left, MnozeniePrzezZeroII, PlusZero, NastepnikPrzezSume,LacznoscDodawania, ←base]
            rfl
theorem IstnienieRozkladuLiczbyNaturalnej : ∀(n m : SierpNat),0<m → ∃(d r : SierpNat), n =m*d + r ∧ r<m:= by
    intro n m hm
    apply Exists.intro (Wynikdzielnienia n m)
    apply Exists.intro (reszta n m)
    exact And.intro (WlasnosciRozkladu n m hm) (WlasciwosciResztyI n m hm)
theorem lemmaDodawanieDoNierwonscJednostronne : ∀ (n m k), n<m → n<m+k := by
    intro n m k h
    induction k with
        | zero =>
            change n<m+0
            rw [PlusZero]
            exact h
        | S k base =>
            change n<m+S k
            have krok1 := DodawanieDoNierownosciOstr n (m+k) (S 0) (S 0) (And.intro base (OdejmowanieOgraniczoneTychSamych (S 0)))
            rw [←NastepnikPrzezSume, ←NastepnikPrzezSume] at krok1
            rw [PrzemiennoscDodawania, lemmaDodawaniaNast]
            have krok2 : n < S n := by
                have step1 : n∸(S n) = 0 := by
                    rw [NastepnikPrzezSume]
                    exact OdejmowanieOgraniczoneOdMniejszej n (S 0)
                have step2 := (Twierdzenie1 n)
                exact And.intro step1 step2
            have krok3 := WlasnosciNierownosciOstrejPrzechodniosc n (S n) (S (m+k)) (And.intro krok2 krok1)
            rw [PrzemiennoscDodawania]
            exact krok3
theorem lemmaMnozenieJednostronneNierw : ∀(n m k:SierpNat), n<m ∧ k≠0 → n<m*k := by
    intro n m k h
    induction k with
        | zero =>
            exact False.elim (h.right (Eq.refl SierpNat.zero))
        | S k base =>
            by_cases hk : k =0
            have step1 : k.S = 1 := by
                rw [hk]
                rfl
            rw [step1,PrzemiennoscMnozenia, IstnienieJednosci]
            exact h.left
            have step1 := base (And.intro h.left hk)
            rw [PrawMnozenia]
            have krok1 : m≠0 := by
                apply Classical.byContradiction
                intro hn
                rw [←PrawaL.PrawPodwojnegoPrzeczenia] at hn
                have step2 := OdejmowanieOgraniczoneOdZera n
                rw [←hn] at step2
                conv at step2 =>
                    right
                    rw [hn]
                have step3 := RownoscPrzezOdejmOgraniczone n m (And.intro h.left.left step2)
                exact h.left.right step3
            have krok2 := (And.intro (And.intro step1 krok1) hk)
            rw [PrawaL.LaczanoscKoniunkcji] at krok2
            exact lemmaDodawanieDoNierwonscJednostronne n (m*k) m step1
theorem lemmaWynikanieZMnozeniaRow : ∀(n m k l:SierpNat), n*l = n*m + k ∧ n≠0 → (∃g:SierpNat, k = n*g) ∧ m≤l := by
    intro n m k l h
    have krok1 : m≤l := by
        apply Classical.byContradiction
        intro hn
        have step1 := lemmaNegNierwonosciSlab m l hn
        have step2 := lemmaMnozenieNierowOstr l m n (And.intro step1 h.right)
        have step3 := lemmaDodawanieDoNierwonscJednostronne (l*n) (m*n) k step2
        rw[ PrzemiennoscMnozenia, PrzemiennoscMnozenia m n] at step3
        exact (step3.right h.left)
    have krok2 := (OdejmowanieOgraniczoneWlasnosciWieksz m l).mp krok1
    have ⟨g , hg⟩ := krok2
    have krok3 := h.left
    rw [hg, RozdzielnoscMnozeniaL, PrzemiennoscDodawania, PrzemiennoscDodawania (n*m) k] at krok3
    have krok4 := PrawSkracaniaRow (n*g) k (n*m) krok3
    exact And.intro (Exists.intro g (Eq.comm.mp krok4)) krok1
theorem JednoznaczneWyznaczenieRozkladu : ∀(n m d1 d2 r1 r2: SierpNat), 0<m ∧ (n = m*d1 + r1) ∧ (n = m*d2 + r2)
∧ (r1<m) ∧ (r2<m) → d1 = d2 ∧ r1 = r2 := by
    intro n m d1 d2 r1 r2 h
    have ⟨h1,h2,h3,h4,h5⟩ := h
    apply Classical.byContradiction
    intro hn
    rw [PrawaL.PrawMorgana2] at hn
    cases hn with
        | inl hl =>
            by_cases rw : d1≤d2
            have step1 : d1<d2 := And.intro rw hl
            have step2 : 0 = n∸n := Eq.comm.mp (OdejmowanieOgraniczoneTychSamych n)
            conv at step2 =>
                right
                conv =>
                    right
                    rw [h2]
                conv =>
                    left
                    rw [h3]
            have step3 := (OdejmowanieOgraniczoneWlasnosciWieksz d1 d2).mp step1.left
            have ⟨k, hk⟩ := step3
            have step7 : k ≠ 0 := by
                apply Classical.byContradiction
                intro k2
                rw [ne_eq, ←PrawaL.PrawPodwojnegoPrzeczenia] at k2
                rw [k2, PlusZero, eq_comm] at hk
                exact step1.right hk
            rw [hk, RozdzielnoscMnozeniaL, ←LacznoscDodawania, eq_comm] at step2
            rw [PrzemiennoscDodawania] at step2
            conv at step2 =>
                left
                conv =>
                    right
                    rw [PrzemiennoscDodawania]
            have krok1 := lemmaNierowOstrNaNast d1 d2 step1
            have krok2 := WlasnosciNierownosciSlabejZwrotnosc r1
            have krok3 := lemmaMnozenieNierownPraw (S d1) d2 m krok1
            have krok4 := lemmaOdejmowanOgran (m*k + r2) (r1) (m*d1) step2
            have krok5 : (m*k + r2)≤ r1 := krok4
            by_cases g : r2 =0
            rw [g, PlusZero] at krok5
            have krok6 := lemmaNierowOstrNaNast r1 m h4
            have krok7 : m≤m*k := by
                by_cases hg : 1≤k
                have step8 := lemmaMnozenieNierownPraw 1 k m hg
                rw [IstnienieJednosci, PrzemiennoscMnozenia] at step8
                exact step8
                have step4 := lemmaNegNierwonosciSlab 1 k hg
                have step5 : k = 0 := by
                    simp at step4
                    have ⟨ g1, g2⟩ := step4
                    have step6 := OdejmowanieOgraniczoneJednosci k
                    rw [step6] at g1
                    cases k with
                        | zero =>
                            rfl
                        | S k =>
                            simp at g1
                            rw [g1] at g2
                            change ¬1=1 at g2
                            have step7 := Eq.refl SierpNat.zero.S
                            change 1=1 at step7
                            exact False.elim (g2 step7)
                exact False.elim (step7 step5)
            have krok8 := WlasnosciNierownosciSlabejPrzechodniosc m (m*k) r1 (And.intro krok7 krok5)
            have krok9 := RownoscPrzezOdejmOgraniczone r1 m (And.intro h4.left krok8)
            exact h4.right krok9
            have krok6 : m≤m*k + r2 := by
                have krok7 := Twierdzenie2 k step7
                have ⟨j, hj⟩ := krok7
                rw [hj, PrawMnozenia,←LacznoscDodawania, PrzemiennoscDodawania, ←LacznoscDodawania]
                exact OdejmowanieOgraniczoneOdMniejszej m (r2 + m*j)
            have krok7 := WlasnosciNierownosciSlabejPrzechodniosc m (m*k + r2) r1 (And.intro krok6 krok5)
            have krok8 := RownoscPrzezOdejmOgraniczone r1 m (And.intro h4.left krok7)
            exact h4.right krok8
            have krok1 := lemmaNegNierwonosciSlab d1 d2 rw
            have krok2 := (OdejmowanieOgraniczoneWlasnosciWieksz d2 d1).mp krok1.left
            have ⟨k, hk⟩ := krok2
            have krok3 : k≠0 := by
                apply Classical.byContradiction
                intro kz
                rw [ne_eq, ←PrawaL.PrawPodwojnegoPrzeczenia] at kz
                rw [kz, PlusZero, eq_comm] at hk
                exact krok1.right hk
            have krok4 : m*d2+r2 < m*d1 + r1 := by
                have step1 := OdejmowanieOgraniczoneTychSamych n
                conv at step1 =>
                    left
                    conv =>
                        left
                        rw [h3]
                    conv =>
                        right
                        rw [h2]
                have step2 : m*d2+r2 ≠ m*d1 + r1 := by
                    rw [hk, RozdzielnoscMnozeniaL, ←LacznoscDodawania, PrzemiennoscDodawania (m*d2), PrzemiennoscDodawania (m*d2)] at step1
                    have step3 := lemmaOdejmowanOgran r2 (m*k + r1) (m*d2) step1
                    have step4 : r2<(m*k+r1) := by
                        apply Classical.byContradiction
                        intro ab
                        rw [NierownoscOstra, PrawaL.PrawMorgana2] at ab
                        have step6 :=((@PrawaL.PrawPodwojnegoPrzeczenia (r2∸(m*k +r1) = 0)).mp step3)
                        have step5 := PrawaL.PrawWnioskowaniaZAlternatyw (¬(r2∸(m*k+r1))=0) (¬r2≠m*k+r1) (And.intro step6 ab)
                        rw [ne_eq, ←PrawaL.PrawPodwojnegoPrzeczenia] at step5
                        have step8 := lemmaMnozenieJednostronneNierw r2 m k (And.intro h5 krok3)
                        have step7 := lemmaDodawanieDoNierwonscJednostronne r2 (m*k) r1 step8
                        exact step7.right step5
                    have krok4 := Eq.refl n
                    conv at krok4 =>
                        left
                        rw [h3]
                    conv at krok4 =>
                        right
                        rw [h2]
                    rw [hk, RozdzielnoscMnozeniaL, ←LacznoscDodawania, PrzemiennoscDodawania, PrzemiennoscDodawania (m*d2)] at krok4
                    have krok5 := PrawSkracaniaRow r2 (m*k +r1) (m*d2) krok4
                    exact False.elim (step4.right krok5)
                have krok4 :(m*d2 + r2)∸(m*d1 + r1) = 0 := by
                    rw [←h2, ←h3]
                    exact OdejmowanieOgraniczoneTychSamych n
                exact (And.intro krok4 step2)
            have krok5 : m*d2 + r2 = m*d1 + r1 := by
                rw [←h2,←h3]
            exact krok4.right krok5
        | inr hr =>
            by_cases hr1: r1<r2
            have krok1 := (OdejmowanieOgraniczoneWlasnosciWieksz r1 r2).mp hr1.left
            have ⟨k, hk⟩ := krok1
            have krok2 : k ≠ 0 := by
                apply Classical.byContradiction
                intro h
                rw [ne_eq, ←PrawaL.PrawPodwojnegoPrzeczenia] at h
                rw [h, PlusZero] at hk
                exact hr1.right (eq_comm.mp hk)
            have krok3 : n∸n = 0 := OdejmowanieOgraniczoneTychSamych n
            conv at krok3 =>
                left
                conv =>
                    left
                    rw [h2]
                conv =>
                    right
                    rw [h3]
                rw [hk]
            rw [PrzemiennoscDodawania r1 k, LacznoscDodawania] at krok3
            have krok4 := lemmaOdejmowanOgran (m*d1) (m*d2 + k) r1 krok3
            have krok5 : n∸n = 0 := OdejmowanieOgraniczoneTychSamych n
            conv at krok5 =>
                left
                conv =>
                    left
                    rw [h3]
                conv =>
                    right
                    rw [h2]
                rw [hk]
            rw [PrzemiennoscDodawania r1 k, LacznoscDodawania] at krok5
            have krok6:= lemmaOdejmowanOgran (m*d2 + k) (m*d1) r1 krok5
            have krok7 := RownoscPrzezOdejmOgraniczone (m*d1) (m*d2 + k) (And.intro krok4 krok6)
            have krok8 := lemmaWynikanieZMnozeniaRow m d2 k d1 (And.intro krok7 (ne_comm.mp h1.right))
            have ⟨g , hg⟩ := krok8.left
            have step1 : k<m := by
                have step2 : k<r2 := by
                    constructor
                    · rw [hk, PrzemiennoscDodawania]
                      exact (OdejmowanieOgraniczoneOdMniejszej k r1)
                    · apply Classical.byContradiction
                      intro hn
                      rw [ne_eq,←PrawaL.PrawPodwojnegoPrzeczenia] at hn
                      have step2 : g≠0 := by
                        apply Classical.byContradiction
                        intro hng
                        rw [ne_eq,←PrawaL.PrawPodwojnegoPrzeczenia] at hng
                        rw [hng,MnozeniePrzezZeroII] at hg
                        exact krok2 hg
                      rw [hn] at hg
                      have step3 : r2<m*g := lemmaMnozenieJednostronneNierw r2 m g (And.intro h5 step2)
                      exact step3.right hg
                exact (WlasnosciNierownosciOstrejPrzechodniosc k r2 m (And.intro step2 h5))
            have step3 :g≠0 := by
                apply Classical.byContradiction
                intro hng
                rw [ne_eq,←PrawaL.PrawPodwojnegoPrzeczenia] at hng
                rw [hng,MnozeniePrzezZeroII] at hg
                exact krok2 hg
            have step2 := lemmaMnozenieJednostronneNierw k m g (And.intro step1 step3)
            exact step2.right hg
            rw [NierownoscOstra, PrawaL.PrawMorgana2, ne_eq, ←PrawaL.PrawPodwojnegoPrzeczenia, PrawaL.PrzemiennoscAlternatywy] at hr1
            have krok1 := PrawaL.PrawWnioskowaniaZAlternatyw (r1=r2) (¬(r1∸r2=0)) (And.intro hr hr1)
            have krok2 := lemmaNegNierwonosciSlab r1 r2 krok1
            have krok3 := (OdejmowanieOgraniczoneWlasnosciWieksz r2 r1).mp krok2.left
            have ⟨k, hk⟩ := krok3
            have krok4 : k ≠ 0 := by
                apply Classical.byContradiction
                intro h
                rw [ne_eq, ←PrawaL.PrawPodwojnegoPrzeczenia] at h
                rw [h, PlusZero] at hk
                exact krok2.right (eq_comm.mp hk)
            have krok5 : n∸n = 0 := OdejmowanieOgraniczoneTychSamych n
            conv at krok5 =>
                left
                conv =>
                    left
                    rw [h2]
                conv =>
                    right
                    rw [h3]
                rw [hk]
            rw [PrzemiennoscDodawania r2 k, LacznoscDodawania] at krok5
            have krok6 := lemmaOdejmowanOgran (m*d1+k) (m*d2) r2 krok5
            have krok7 : n∸n = 0 := OdejmowanieOgraniczoneTychSamych n
            conv at krok7 =>
                left
                conv =>
                    left
                    rw [h3]
                conv =>
                    right
                    rw [h2]
                rw [hk]
            rw [PrzemiennoscDodawania r2 k, LacznoscDodawania] at krok7
            have krok8:= lemmaOdejmowanOgran (m*d2) (m*d1+k) r2 krok7
            have krok9 := RownoscPrzezOdejmOgraniczone (m*d1+k) (m*d2) (And.intro krok6 krok8)
            have krok10 := lemmaWynikanieZMnozeniaRow m d1 k d2 (And.intro (eq_comm.mp krok9) (ne_comm.mp h1.right))
            have ⟨g , hg⟩ := krok10.left
            have step1 : k<m := by
                have step2 : k<r1 := by
                    constructor
                    · rw [hk, PrzemiennoscDodawania]
                      exact (OdejmowanieOgraniczoneOdMniejszej k r2)
                    · apply Classical.byContradiction
                      intro hn
                      rw [ne_eq,←PrawaL.PrawPodwojnegoPrzeczenia] at hn
                      have step2 : g≠0 := by
                        apply Classical.byContradiction
                        intro hng
                        rw [ne_eq,←PrawaL.PrawPodwojnegoPrzeczenia] at hng
                        rw [hng,MnozeniePrzezZeroII] at hg
                        exact krok4 hg
                      rw [hn] at hg
                      have step3 : r1<m*g := lemmaMnozenieJednostronneNierw r1 m g (And.intro h4 step2)
                      exact step3.right hg
                exact (WlasnosciNierownosciOstrejPrzechodniosc k r1 m (And.intro step2 h4))
            have step3 :g≠0 := by
                apply Classical.byContradiction
                intro hng
                rw [ne_eq,←PrawaL.PrawPodwojnegoPrzeczenia] at hng
                rw [hng,MnozeniePrzezZeroII] at hg
                exact krok4 hg
            have step2 := lemmaMnozenieJednostronneNierw k m g (And.intro step1 step3)
            exact step2.right hg
