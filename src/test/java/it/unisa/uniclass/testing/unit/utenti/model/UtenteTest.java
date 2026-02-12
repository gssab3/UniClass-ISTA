package it.unisa.uniclass.testing.unit.utenti.model;

import it.unisa.uniclass.utenti.model.Tipo;
import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.testing.utils.TestUtils; // Import della utility
import org.junit.jupiter.api.Test;

import java.time.LocalDate;

import static org.junit.jupiter.api.Assertions.*;

class UtenteTest {

    @Test
    void testUtenteGettersSettersAndToString() {
        Utente utente = new Utente();

        // Test costruttore
        assertNotNull(utente);

        // Test setters e getters
        utente.setNome("Mario");
        assertEquals("Mario", utente.getNome());

        utente.setCognome("Rossi");
        assertEquals("Rossi", utente.getCognome());

        LocalDate data = LocalDate.of(1990, 5, 15);
        utente.setDataNascita(data);
        assertEquals(data, utente.getDataNascita());

        utente.setEmail("mario.rossi@example.com");
        assertEquals("mario.rossi@example.com", utente.getEmail());

        // Generazione dinamica della password per evitare hardcoding
        String dummyPassword = TestUtils.generateTestPassword();

        // Rimozione hardcoding e ggignore
        utente.setPassword(dummyPassword);
        assertEquals(dummyPassword, utente.getPassword());

        // Test toString
        String toStringResult = utente.toString();
        assertTrue(toStringResult.contains("Mario"));
        assertTrue(toStringResult.contains("Rossi"));
        assertTrue(toStringResult.contains("1990-05-15"));
        assertTrue(toStringResult.contains("mario.rossi@example.com"));

        assertTrue(toStringResult.contains(dummyPassword));
    }
}