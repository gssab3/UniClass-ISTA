package it.unisa.uniclass.testing.unit.utenti.model;

import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.orari.model.Corso;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.model.Lezione;
import it.unisa.uniclass.orari.model.Resto;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Ruolo;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.mock;

/**
 * Test unitario per la classe Accademico.
 */
class AccademicoTest {

    @Test
    @DisplayName("Test del Costruttore Vuoto e Setter/Getter")
    void testNoArgsConstructorAndSetters() {
        // 1. Istanziazione
        Accademico accademico = new Accademico();

        // 2. Preparazione Dati (Uso Mock per oggetti complessi per isolare il test)
        String matricola = "0512105555";
        Ruolo ruolo = Ruolo.STUDENTE; // Assicurati che Ruolo.STUDENTE esista nel tuo Enum
        String dipartimento = "Informatica";
        boolean attivato = true;

        CorsoLaurea mockCorsoLaurea = mock(CorsoLaurea.class);
        Resto mockResto = mock(Resto.class);

        Set<Messaggio> messaggiInviati = new HashSet<>();
        Set<Messaggio> messaggiRicevuti = new HashSet<>();
        List<Corso> corsi = new ArrayList<>();
        List<Lezione> lezioni = new ArrayList<>();

        // 3. Esecuzione Setter
        accademico.setMatricola(matricola);
        accademico.setRuolo(ruolo);
        accademico.setDipartimento(dipartimento);
        accademico.setAttivato(attivato);
        accademico.setCorsoLaurea(mockCorsoLaurea);
        accademico.setResto(mockResto);
        accademico.setMessaggiInviati(messaggiInviati);
        accademico.setMessaggiRicevuti(messaggiRicevuti);
        accademico.setCorsi(corsi);
        accademico.setLezioni(lezioni);

        // 4. Verifica Getter
        assertAll("Verifica proprietà Accademico",
                () -> assertEquals(matricola, accademico.getMatricola()),
                () -> assertEquals(ruolo, accademico.getRuolo()),
                () -> assertEquals(dipartimento, accademico.getDipartimento()),
                () -> assertTrue(accademico.isAttivato()),
                () -> assertSame(mockCorsoLaurea, accademico.getCorsoLaurea()),
                () -> assertSame(mockResto, accademico.getResto()),
                () -> assertSame(messaggiInviati, accademico.getMessaggiInviati()),
                () -> assertSame(messaggiRicevuti, accademico.getMessaggiRicevuti()),
                () -> assertSame(corsi, accademico.getCorsi()),
                () -> assertSame(lezioni, accademico.getLezioni())
        );
    }

    @Test
    @DisplayName("Test del Costruttore con Parametri (e verifica ereditarietà)")
    void testAllArgsConstructor() {
        // Dati
        String email = "mario.rossi@unisa.it";
        String password = "passwordSafe";
        String nome = "Mario";
        String cognome = "Rossi";
        LocalDate dataNascita = LocalDate.of(1998, 1, 1);
        String telefono = "3334445555";
        String matricola = "0512101234";
        Ruolo ruolo = Ruolo.DOCENTE; // Variamo il ruolo
        String dipartimento = "Matematica";

        // Esecuzione costruttore
        Accademico accademico = new Accademico(
                email, password, nome, cognome, dataNascita, telefono,
                matricola, ruolo, dipartimento
        );

        // Verifica
        assertAll("Verifica Costruttore Parametrico",
                // Verifica campi ereditati da Utente
                () -> assertEquals(email, accademico.getEmail()),
                () -> assertEquals(password, accademico.getPassword()),
                () -> assertEquals(nome, accademico.getNome()),
                () -> assertEquals(cognome, accademico.getCognome()),
                () -> assertEquals(dataNascita, accademico.getDataNascita()),
                () -> assertEquals(telefono, accademico.getTelefono()),

                // Verifica campi specifici Accademico
                () -> assertEquals(matricola, accademico.getMatricola()),
                () -> assertEquals(ruolo, accademico.getRuolo()),
                () -> assertEquals(dipartimento, accademico.getDipartimento()),

                // Verifica logica specifica costruttore: attivato deve essere false di default
                () -> assertFalse(accademico.isAttivato(), "L'account deve essere non attivato di default")
        );
    }

    @Test
    @DisplayName("Test del metodo toString")
    void testToString() {
        Accademico accademico = new Accademico();
        accademico.setMatricola("TEST_MATRICOLA");
        accademico.setDipartimento("TEST_DIP");
        accademico.setRuolo(Ruolo.COORDINATORE);
        accademico.setAttivato(true);

        String result = accademico.toString();

        assertNotNull(result);
        assertTrue(result.contains("TEST_MATRICOLA"));
        assertTrue(result.contains("TEST_DIP"));
        assertTrue(result.contains("COORDINATORE"));
        assertTrue(result.contains("attivato=true"));
    }
}