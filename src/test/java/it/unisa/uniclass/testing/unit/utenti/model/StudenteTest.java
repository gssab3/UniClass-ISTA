package it.unisa.uniclass.testing.unit.utenti.model;

import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.model.Resto;
import it.unisa.uniclass.utenti.model.Tipo;
import org.junit.jupiter.api.Test;

import java.time.LocalDate;

import static org.junit.jupiter.api.Assertions.*;

class StudenteTest {

    @Test
    void testCostruttoreVuoto() {
        Studente s = new Studente();

        // Controlla il tipo impostato dal costruttore di default
        assertEquals(Tipo.Studente, s.getTipo());

        // Liste e campi ereditati non nulli

        assertNotNull(s.getMessaggiInviati());
        assertNotNull(s.getMessaggiRicevuti());
    }

    @Test
    void testCostruttoreParametrico() {
        LocalDate dataNascita = LocalDate.of(2000, 1, 1);
        LocalDate iscrizione = LocalDate.of(2022, 10, 1);
        CorsoLaurea corsoLaurea = new CorsoLaurea();
        Resto resto = new Resto();

        Studente s = new Studente(
                "Luca",
                "Bianchi",
                dataNascita,
                "l.bianchi@example.com",
                "password123",
                "MAT456",
                iscrizione,
                corsoLaurea,
                resto
        );

        // Verifica valori tramite getter
        assertEquals("Luca", s.getNome());
        assertEquals("Bianchi", s.getCognome());
        assertEquals(dataNascita, s.getDataNascita());
        assertEquals("l.bianchi@example.com", s.getEmail());
        assertEquals("password123", s.getPassword());
        assertEquals("MAT456", s.getMatricola());
        assertEquals(iscrizione, s.getIscrizione());
        assertEquals(corsoLaurea, s.getCorsoLaurea());
        assertEquals(Tipo.Studente, s.getTipo());
        assertEquals(resto, s.getResto());
    }

    @Test
    void testSetterGetterResto() {
        Studente s = new Studente();
        Resto resto = new Resto();

        s.setResto(resto);
        assertEquals(resto, s.getResto());
    }

    @Test
    void testToStringNonNull() {
        Studente s = new Studente();
        assertNotNull(s.toString());
        assertTrue(s.toString().contains("Studente") || s.toString().contains("nome"));
    }
}
