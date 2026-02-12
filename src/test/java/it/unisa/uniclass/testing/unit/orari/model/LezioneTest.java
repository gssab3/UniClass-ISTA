package it.unisa.uniclass.testing.unit.orari.model;

import it.unisa.uniclass.orari.model.*;
import it.unisa.uniclass.utenti.model.Accademico;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Field;
import java.sql.Time;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class LezioneTest {

    @Test
    @DisplayName("Test Costruttore Vuoto e Setter/Getter")
    void testNoArgsConstructorAndSetters() throws Exception {
        Lezione l = new Lezione();

        // Reflection per ID (privato senza setter pubblico nel codice fornito, ma usato da JPA)
        Field idField = Lezione.class.getDeclaredField("id");
        idField.setAccessible(true);
        idField.set(l, 100L);

        int semestre = 1;
        Time start = Time.valueOf("09:00:00");
        Time end = Time.valueOf("11:00:00");
        Giorno giorno = Giorno.LUNEDI; // Assumo che Giorno sia un Enum
        Corso corso = new Corso();
        Resto resto = new Resto();
        Aula aula = new Aula();
        List<Accademico> accs = new ArrayList<>();

        l.setSemestre(semestre);
        l.setOraInizio(start);
        l.setOraFine(end);
        l.setGiorno(giorno);
        l.setCorso(corso);
        l.setResto(resto);
        l.setAula(aula);
        l.setAccademici(accs);

        assertAll(
                () -> assertEquals(100L, l.getId()),
                () -> assertEquals(semestre, l.getSemestre()),
                () -> assertEquals(start, l.getOraInizio()),
                () -> assertEquals(end, l.getOraFine()),
                () -> assertEquals(giorno, l.getGiorno()),
                () -> assertSame(corso, l.getCorso()),
                () -> assertSame(resto, l.getResto()),
                () -> assertSame(aula, l.getAula()),
                () -> assertSame(accs, l.getAccademici())
        );
    }

    @Test
    @DisplayName("Test Costruttore Parametrico")
    void testAllArgsConstructor() {
        int semestre = 2;
        Time start = Time.valueOf("14:00:00");
        Time end = Time.valueOf("16:00:00");
        Giorno giorno = Giorno.MARTEDI;
        Resto resto = new Resto();
        Corso corso = new Corso();
        Aula aula = new Aula();

        Lezione l = new Lezione(semestre, start, end, giorno, resto, corso, aula);

        assertAll(
                () -> assertEquals(semestre, l.getSemestre()),
                () -> assertEquals(start, l.getOraInizio()),
                () -> assertEquals(end, l.getOraFine()),
                () -> assertEquals(giorno, l.getGiorno()),
                () -> assertSame(resto, l.getResto()),
                () -> assertSame(corso, l.getCorso()),
                () -> assertSame(aula, l.getAula())
        );
    }

    @Test
    @DisplayName("Test toString")
    void testToString() {
        Lezione l = new Lezione();
        l.setSemestre(1);
        String s = l.toString();
        assertNotNull(s);
        assertTrue(s.contains("semestre=1"));
        assertTrue(s.contains("Lezione{"));
    }
}