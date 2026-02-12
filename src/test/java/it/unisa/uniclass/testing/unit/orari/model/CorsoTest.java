package it.unisa.uniclass.testing.unit.orari.model;

import it.unisa.uniclass.orari.model.*;
import it.unisa.uniclass.utenti.model.Accademico;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class CorsoTest {

    @Test
    @DisplayName("Test Costruttore Vuoto e Setter/Getter")
    void testNoArgsConstructorAndSetters() throws Exception {
        Corso c = new Corso();

        // Reflection per ID (no public setter)
        Field idField = Corso.class.getDeclaredField("id");
        idField.setAccessible(true);
        idField.set(c, 50L);

        String nome = "Analisi I";
        CorsoLaurea cl = new CorsoLaurea();
        AnnoDidattico ad = new AnnoDidattico();
        List<Lezione> lezioni = new ArrayList<>();
        List<Accademico> accs = new ArrayList<>();

        c.setNome(nome);
        c.setCorsoLaurea(cl);
        c.setAnnoDidattico(ad);
        c.setLezioni(lezioni);
        c.setAccademici(accs);

        assertAll(
                () -> assertEquals(50L, c.getId()),
                () -> assertEquals(nome, c.getNome()),
                () -> assertSame(cl, c.getCorsoLaurea()),
                () -> assertSame(ad, c.getAnnoDidattico()),
                () -> assertSame(lezioni, c.getLezioni()),
                () -> assertSame(accs, c.getAccademici())
        );
    }

    @Test
    @DisplayName("Test Costruttore Parametrico (Nome)")
    void testConstructorWithName() {
        String nome = "Fisica";
        Corso c = new Corso(nome);

        assertEquals(nome, c.getNome());
        assertNotNull(c.getLezioni(), "Le lezioni dovrebbero essere inizializzate");
        assertNotNull(c.getAccademici(), "Gli accademici dovrebbero essere inizializzati");
    }

    @Test
    @DisplayName("Test toString")
    void testToString() {
        Corso c = new Corso("TestName");
        String s = c.toString();
        assertTrue(s.contains("TestName"));
        assertTrue(s.contains("Corso{"));
    }
}