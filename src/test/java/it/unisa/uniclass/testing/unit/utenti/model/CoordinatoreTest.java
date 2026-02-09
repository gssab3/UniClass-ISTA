package it.unisa.uniclass.testing.unit.utenti.model;

import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.utenti.model.Tipo;
import org.junit.jupiter.api.Test;

import java.time.LocalDate;

import static org.junit.jupiter.api.Assertions.*;

class CoordinatoreTest {

    @Test
    void testCostruttoreVuoto() {
        Coordinatore c = new Coordinatore();

        // Verifica che il tipo sia corretto
        assertEquals(Tipo.Coordinatore, c.getTipo());

        // Liste inizializzate dal super
        assertNotNull(c.getCorsi());
        assertTrue(c.getCorsi().isEmpty());
        assertNotNull(c.getLezioni());
        assertTrue(c.getLezioni().isEmpty());
    }

    @Test
    void testCostruttoreParametrico() {
        LocalDate dataNascita = LocalDate.of(1980, 1, 1);
        LocalDate iscrizione = LocalDate.of(2020, 10, 1);
        CorsoLaurea corsoLaurea = new CorsoLaurea();

        Coordinatore c = new Coordinatore(
                "Mario",
                "Rossi",
                dataNascita,
                "m.rossi@example.com",
                "password",
                "MAT123",
                iscrizione,
                corsoLaurea,
                "Informatica"
        );

        // Verifica valori tramite getter
        assertEquals("Mario", c.getNome());
        assertEquals("Rossi", c.getCognome());
        assertEquals(dataNascita, c.getDataNascita());
        assertEquals("m.rossi@example.com", c.getEmail());
        assertEquals("password", c.getPassword());
        assertEquals("MAT123", c.getMatricola());
        assertEquals(iscrizione, c.getIscrizione());
        assertEquals(corsoLaurea, c.getCorsoLaurea());
        assertEquals("Informatica", c.getDipartimento());
        assertEquals(Tipo.Coordinatore, c.getTipo());

        // Liste inizializzate
        assertNotNull(c.getCorsi());
        assertTrue(c.getCorsi().isEmpty());
        assertNotNull(c.getLezioni());
        assertTrue(c.getLezioni().isEmpty());
    }

    @Test
    void testToStringNonNull() {
        Coordinatore c = new Coordinatore();
        assertNotNull(c.toString());
        assertTrue(c.toString().contains("Coordinatore") || c.toString().contains("nome"));
    }
}
