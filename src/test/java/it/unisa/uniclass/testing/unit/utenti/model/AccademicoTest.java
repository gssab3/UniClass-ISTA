package it.unisa.uniclass.testing.unit.utenti.model;


import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.orari.model.Corso;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.model.Lezione;
import it.unisa.uniclass.orari.model.Resto;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Ruolo;
import org.junit.jupiter.api.Test;

import java.time.LocalDate;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

class AccademicoTest {

    @Test
    void testDefaultConstructor_initializesCollections() {
        Accademico a = new Accademico();

        assertNotNull(a.getMessaggiInviati());
        assertNotNull(a.getMessaggiRicevuti());
        assertNotNull(a.getCorsi());
        assertNotNull(a.getLezioni());

        assertTrue(a.getMessaggiInviati().isEmpty());
        assertTrue(a.getMessaggiRicevuti().isEmpty());
        assertTrue(a.getCorsi().isEmpty());
        assertTrue(a.getLezioni().isEmpty());
    }

    @Test
    void testFullConstructor_setsAllFieldsCorrectly() {
        LocalDate data = LocalDate.of(1990, 1, 1);

        Accademico a = new Accademico(
                "email@test.it",
                "pwd",
                "Mario",
                "Rossi",
                data,
                "3331234567",
                "MAT123",
                Ruolo.DOCENTE,
                "DIEM"
        );

        assertEquals("email@test.it", a.getEmail());
        assertEquals("pwd", a.getPassword());
        assertEquals("Mario", a.getNome());
        assertEquals("Rossi", a.getCognome());
        assertEquals(data, a.getDataNascita());
        assertEquals("3331234567", a.getTelefono());
        assertEquals("MAT123", a.getMatricola());
        assertEquals(Ruolo.DOCENTE, a.getRuolo());
        assertEquals("DIEM", a.getDipartimento());
        assertFalse(a.isAttivato()); // default impostato nel costruttore
    }

    @Test
    void testSettersAndGetters() {
        Accademico a = new Accademico();

        a.setMatricola("M1");
        a.setRuolo(Ruolo.STUDENTE);
        a.setDipartimento("Informatica");

        CorsoLaurea cl = new CorsoLaurea();
        a.setCorsoLaurea(cl);

        Resto r = new Resto();
        a.setResto(r);

        Set<Messaggio> inviati = Set.of(new Messaggio());
        Set<Messaggio> ricevuti = Set.of(new Messaggio());
        List<Corso> corsi = List.of(new Corso());
        List<Lezione> lezioni = List.of(new Lezione());

        a.setMessaggiInviati(inviati);
        a.setMessaggiRicevuti(ricevuti);
        a.setCorsi(corsi);
        a.setLezioni(lezioni);
        a.setAttivato(true);

        assertEquals("M1", a.getMatricola());
        assertEquals(Ruolo.STUDENTE, a.getRuolo());
        assertEquals("Informatica", a.getDipartimento());
        assertEquals(cl, a.getCorsoLaurea());
        assertEquals(r, a.getResto());
        assertEquals(inviati, a.getMessaggiInviati());
        assertEquals(ricevuti, a.getMessaggiRicevuti());
        assertEquals(corsi, a.getCorsi());
        assertEquals(lezioni, a.getLezioni());
        assertTrue(a.isAttivato());
    }

    @Test
    void testToString_containsKeyFields() {
        Accademico a = new Accademico();
        a.setMatricola("M1");
        a.setRuolo(Ruolo.COORDINATORE);
        a.setDipartimento("DIEM");

        String s = a.toString();

        assertTrue(s.contains("M1"));
        assertTrue(s.contains("COORDINATORE"));
        assertTrue(s.contains("DIEM"));
    }
}
