package it.unisa.uniclass.testing.unit.utenti.model;

import it.unisa.uniclass.utenti.model.PersonaleTA;
import org.junit.jupiter.api.Test;

import java.time.LocalDate;

import static org.junit.jupiter.api.Assertions.*;

class PersonaleTATest {

    @Test
    void testPersonaleTAConstructorsGettersSettersAndToString() {
        // Test costruttore vuoto
        PersonaleTA taVuoto = new PersonaleTA();
        assertNotNull(taVuoto);

        // Test costruttore completo
        LocalDate data = LocalDate.of(1985, 12, 1);
        PersonaleTA taCompleto = new PersonaleTA("Luca", "Bianchi", data, "luca.bianchi@example.com", "pass123", "3331234567");
        assertNotNull(taCompleto);
        assertEquals("Luca", taCompleto.getNome());
        assertEquals("Bianchi", taCompleto.getCognome());
        assertEquals(data, taCompleto.getDataNascita());
        assertEquals("luca.bianchi@example.com", taCompleto.getEmail());
        assertEquals("pass123", taCompleto.getPassword());
        assertEquals("3331234567", taCompleto.getTelefono());

        // Test setter e getter telefono
        taCompleto.setTelefono("3337654321");
        assertEquals("3337654321", taCompleto.getTelefono());

        // Test id getter (di default è 0 per oggetto non persistito)
        assertEquals(0L, taCompleto.getId());

        // Test toString
        String toStringResult = taCompleto.toString();
        assertTrue(toStringResult.contains("Luca"));
        assertTrue(toStringResult.contains("Bianchi"));
        assertTrue(toStringResult.contains("1985-12-01"));
        assertTrue(toStringResult.contains("luca.bianchi@example.com"));
        assertTrue(toStringResult.contains("3337654321"));
    }
}
