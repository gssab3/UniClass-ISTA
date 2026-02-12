package it.unisa.uniclass.testing.unit.orari.model;

import it.unisa.uniclass.orari.model.AnnoDidattico;
import it.unisa.uniclass.orari.model.Corso;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.model.Resto;
import it.unisa.uniclass.utenti.model.Accademico;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class CorsoLaureaTest {

    @Test
    @DisplayName("Test Costruttore Vuoto e Default")
    void testNoArgs() throws Exception {
        CorsoLaurea cl = new CorsoLaurea();

        // Verifica inizializzazioni default
        assertNull(cl.getNome());
        assertNotNull(cl.getCorsi());
        assertNotNull(cl.getResti());

        // Reflection ID
        Field idField = CorsoLaurea.class.getDeclaredField("id");
        idField.setAccessible(true);
        idField.set(cl, 1L);

        assertEquals(1L, cl.getId());
    }

    @Test
    @DisplayName("Test Costruttore con Nome")
    void testConstructorName() {
        String nome = "Ingegneria";
        CorsoLaurea cl = new CorsoLaurea(nome);

        assertEquals(nome, cl.getNome());
        assertNotNull(cl.getCorsi()); // Verifico che la lista sia stata inizializzata
    }

    @Test
    @DisplayName("Test Costruttore Completo")
    void testAllArgsConstructor() {
        String nome = "Lettere";
        List<Resto> resti = new ArrayList<>();
        List<AnnoDidattico> anni = new ArrayList<>();

        CorsoLaurea cl = new CorsoLaurea(nome, resti, anni);

        assertEquals(nome, cl.getNome());
        assertSame(resti, cl.getResti());
        assertSame(anni, cl.getAnniDidattici());
        assertNotNull(cl.getCorsi(), "La lista corsi dovrebbe essere inizializzata");
    }

    @Test
    @DisplayName("Test Setter e Getter Liste")
    void testLists() {
        CorsoLaurea cl = new CorsoLaurea();

        List<Corso> corsi = new ArrayList<>();
        List<Accademico> accs = new ArrayList<>();
        List<AnnoDidattico> anni = new ArrayList<>();
        List<Resto> resti = new ArrayList<>();

        cl.setCorsi(corsi);
        cl.setAccademici(accs);
        cl.setAnniDidattici(anni);
        cl.setResti(resti);
        cl.setNome("Nome");

        assertAll(
                () -> assertSame(corsi, cl.getCorsi()),
                () -> assertSame(accs, cl.getAccademici()),
                () -> assertSame(anni, cl.getAnniDidattici()),
                () -> assertSame(resti, cl.getResti()),
                () -> assertEquals("Nome", cl.getNome())
        );
    }

    @Test
    @DisplayName("Test toString")
    void testToString() {
        CorsoLaurea cl = new CorsoLaurea("Info");
        String s = cl.toString();
        assertTrue(s.contains("Info"));
        assertTrue(s.contains("CorsoLaurea{"));
    }
}