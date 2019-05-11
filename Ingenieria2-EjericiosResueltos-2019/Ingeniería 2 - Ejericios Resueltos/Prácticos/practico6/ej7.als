sig Interprete {}
sig Cancion {}

sig Catalogo {
	canciones: set Cancion,
	interpretes: set Interprete,
	interpretaciones: canciones -> interpretes
}{
	//canciones in canciones.(interpretaciones.~interpretaciones)
	//interpretes in interpretes.( (~interpretaciones).interpretaciones)
	canciones = interpretaciones.interpretes
	interpretes = canciones.interpretaciones
}


pred add[cat, cat': Catalogo, c: Cancion, i: Interprete] {
	cat'.canciones = cat.canciones + c
	cat'.interpretes = cat.interpretes + i
	cat'.interpretaciones = cat.interpretaciones + (c->i) 
}


pred del[cat, cat': Catalogo, c: Cancion, i: Interprete] {
	cat != cat' // Para que se muestren ejemplos interesantes
	cat'.interpretaciones = cat.interpretaciones - (c->i) 
	(no (cat'.interpretaciones).i) => (cat'.interpretes = cat.interpretes-i)
	(some (cat'.interpretaciones).i) => (cat'.interpretes = cat.interpretes)

	(no c.(cat'.interpretaciones)) => (cat'.canciones = cat.canciones-c)
	(some c.(cat'.interpretaciones)) => (cat'.canciones = cat.canciones)
}

fun same_song[c: Catalogo]: Interprete->Interprete {
	{(~(c.interpretaciones)).(c.interpretaciones) -  ((c.interpretes)<: iden)  }
}

run del  for 4 but 2 Catalogo
