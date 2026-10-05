Formalizacja Matematyki w Lean 4

	Ten projekt powstał jako narzędzie do nauki matematyki, łączące
	klasyczne polskie podręczniki akademickie z systemem automatycznej
	weryfikacji dowodów Lean 4. Głównym celem było dokładne przerobienie
	materiału z gwarancją, że każdy krok logiczny w zadaniach jest
	poprawny i sprawdzony przez program.

	Repozytorium ma charakter edukacyjny. Udostępniam je z myślą o osobach,
	które studiują z tych samych książek lub uczą się języka Lean 4
	i chciałyby podpatrzeć, jak sformalizować konkretne dowody – zwłaszcza
	te żmudne i wieloliniowe (jak dowody własności różnicy symetrycznej),
	które w podręcznikach bywają pomijane lub skracane.

Zawartość projektu

	Projekt składa się z dwóch głównych działów, opartych na kanonie
	polskiej literatury matematycznej:

	1. Arytmetyka (nat.lean)
	Plik oparty w całości na podręczniku Wacława Sierpińskiego. Przeprowadziłem
	tutaj formalny dowód absolutnie każdego twierdzenia i lematu zawartego w książce
	– od podstawowych aksjomatów Peano, przez fundamentalne własności dodawania,
	mnożenia, potęgowania i odejmowania ograniczonego, aż do momentu wejścia w wielomiany. 

	2. Naiwna Teoria Mnogości (set_basics.lean)
	Plik bazujący na "Teorii mnogości" Kazimierza Kuratowskiego i Andrzeja Mostowskiego.
	Znajduje się tu pełna formalizacja naiwnej teorii mnogości. Zaczynając od udowodnienia
	kilkudziesięciu podstawowych praw rachunku zdań i relacji zbiorów, kod przechodzi
	do weryfikacji bardziej zaawansowanych struktur, takich jak filtry, ideały oraz relacje
	przystawania zbiorów do ideału i filtru.

Cel repozytorium
	Weryfikacja wiedzy matematycznej w środowisku, które nie wybacza luk logicznych.
	Projekt służy jako otwarta baza rozwiązań dla każdego, kto chce zobaczyć, jak klasyczna
	teoria matematyczna przekłada się na ścisły język Proof Assistanta.
