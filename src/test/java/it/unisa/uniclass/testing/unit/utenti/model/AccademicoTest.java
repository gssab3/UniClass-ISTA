package it.unisa.uniclass.testing.unit.utenti.model;

import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Tipo;
import org.junit.jupiter.api.Test;

import java.time.LocalDate;
import java.util.HashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;

class AccademicoTest {

    @Test
    void testCostruttoreVuoto() {
        Accademico a = new Accademico();
        assertFalse(a.isAttivato());
        assertNotNull(a.getMessaggiInviati());
        assertNotNull(a.getMessaggiRicevuti());
    }

    @Test
    void testCostruttoreParametrico() {
        LocalDate nascita = LocalDate.of(1995, 5, 20);
        LocalDate iscrizione = LocalDate.of(2022, 10, 1);
        CorsoLaurea corsoLaurea = new CorsoLaurea();

        Accademico a = new Accademico("Mario", "Rossi", nascita, "m.rossi@example.com", "password", Tipo.Docente);
        a.setMatricola("MAT123");
        a.setIscrizione(iscrizione);
        a.setCorsoLaurea(corsoLaurea);
        a.setAttivato(true);

        assertEquals("Mario", a.getNome());
        assertEquals("Rossi", a.getCognome());
        assertEquals(nascita, a.getDataNascita());
        assertEquals("m.rossi@example.com", a.getEmail());
        assertEquals("password", a.getPassword());
        assertEquals(Tipo.Docente, a.getTipo());

        assertEquals("MAT123", a.getMatricola());
        assertEquals(iscrizione, a.getIscrizione());
        assertEquals(corsoLaurea, a.getCorsoLaurea());
        assertTrue(a.isAttivato());
    }

    @Test
    void testSetterGetterMessaggi() {
        Accademico a = new Accademico();

        Set<Messaggio> inviati = new HashSet<>();
        Set<Messaggio> ricevuti = new HashSet<>();

        a.setMessaggiInviati(inviati);
        a.setMessaggiRicevuti(ricevuti);

        assertEquals(inviati, a.getMessaggiInviati());
        assertEquals(ricevuti, a.getMessaggiRicevuti());
    }
}
