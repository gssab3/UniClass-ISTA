package it.unisa.uniclass.testing.unit.conversazioni.service;

import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.model.Topic;
import it.unisa.uniclass.conversazioni.service.MessaggioService;
import it.unisa.uniclass.conversazioni.service.dao.MessaggioRemote;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.UserDirectory;
import jakarta.persistence.NoResultException;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.time.LocalDateTime;
import java.util.Arrays;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.*;

/**
 * Test Unitario per MessaggioService.
 * Obiettivo: 100% Statement Coverage e 100% Branch Coverage.
 */
@ExtendWith(MockitoExtension.class)
class MessaggioServiceTest {

    @Mock
    private MessaggioRemote messaggioDao;

    @Mock
    private UserDirectory userDirectory;

    @InjectMocks
    private MessaggioService messaggioService;

    // --- TEST INVIA MESSAGGIO ---

    @Test
    @DisplayName("Invia Messaggio: Successo")
    void testInviaMessaggio_Success() throws Exception {
        String emailAutore = "sender@unisa.it";
        String emailDest = "dest@unisa.it";
        String testo = "Ciao";

        Accademico sender = new Accademico();
        Accademico dest = new Accademico();

        when(userDirectory.getUser(emailAutore)).thenReturn(sender);
        when(userDirectory.getUser(emailDest)).thenReturn(dest);

        messaggioService.inviaMessaggio(testo, emailAutore, emailDest);

        verify(messaggioDao).aggiungiMessaggio(any(Messaggio.class));
    }

    @Test
    @DisplayName("Invia Messaggio: Fallimento - Mittente non Accademico")
    void testInviaMessaggio_Fail_SenderNotAccademico() {
        String emailAutore = "admin@unisa.it";
        Utente simpleUser = new Utente(); // Non Accademico

        when(userDirectory.getUser(emailAutore)).thenReturn(simpleUser);
        // Non serve mockare il destinatario, fallisce prima

        Exception exception = assertThrows(IllegalArgumentException.class, () -> {
            messaggioService.inviaMessaggio("txt", emailAutore, "any");
        });

        assertEquals("Il mittente non è abilitato all'invio di messaggi accademici.", exception.getMessage());
        verify(messaggioDao, never()).aggiungiMessaggio(any());
    }

    @Test
    @DisplayName("Invia Messaggio: Fallimento - Destinatario non Accademico")
    void testInviaMessaggio_Fail_DestNotAccademico() {
        String emailAutore = "prof@unisa.it";
        String emailDest = "admin@unisa.it";

        Accademico sender = new Accademico();
        Utente simpleUser = new Utente();

        when(userDirectory.getUser(emailAutore)).thenReturn(sender);
        when(userDirectory.getUser(emailDest)).thenReturn(simpleUser);

        Exception exception = assertThrows(IllegalArgumentException.class, () -> {
            messaggioService.inviaMessaggio("txt", emailAutore, emailDest);
        });

        assertEquals("Il destinatario non è un utente accademico valido.", exception.getMessage());
    }

    // --- TEST TROVA MESSAGGIO (TRY-CATCH COVERAGE) ---

    @Test
    @DisplayName("Trova Messaggio: Trovato")
    void testTrovaMessaggio_Found() {
        Messaggio m = new Messaggio();
        when(messaggioDao.trovaMessaggio(1L)).thenReturn(m);

        Messaggio result = messaggioService.trovaMessaggio(1L);
        assertNotNull(result);
    }

    @Test
    @DisplayName("Trova Messaggio: Non Trovato (Catch NoResultException)")
    void testTrovaMessaggio_NotFound() {
        when(messaggioDao.trovaMessaggio(1L)).thenThrow(new NoResultException());

        Messaggio result = messaggioService.trovaMessaggio(1L);
        assertNull(result, "Deve ritornare null se l'eccezione viene catturata");
    }

    // --- TEST TROVA MESSAGGERI (LOOP & BRANCH COVERAGE) ---

    @Test
    @DisplayName("Trova Messaggeri: Filtra duplicati e autori null")
    void testTrovaMessaggeriDiUnAccademico() {
        String matricola = "001";
        Accademico autore1 = new Accademico(); autore1.setMatricola("A1");
        Accademico autore2 = new Accademico(); autore2.setMatricola("A2");

        Messaggio m1 = new Messaggio(); m1.setAutore(autore1); // Valido
        Messaggio m2 = new Messaggio(); m1.setAutore(null);    // Null (Branch coverage)
        Messaggio m3 = new Messaggio(); m3.setAutore(autore1); // Duplicato (Branch coverage)
        Messaggio m4 = new Messaggio(); m4.setAutore(autore2); // Nuovo valido

        // Nota: uso spy o lista reale. Qui m2 ha autore null.
        // Simuliamo la lista ritornata dal DAO
        List<Messaggio> listaDAO = Arrays.asList(m1, m2, m3, m4);

        // M2 deve avere autore null esplicitamente per sicurezza
        m2.setAutore(null);

        when(messaggioDao.trovaMessaggiRicevuti(matricola)).thenReturn(listaDAO);

        List<Accademico> risultati = messaggioService.trovaMessaggeriDiUnAccademico(matricola);

        // Verifica: Ci devono essere solo 2 autori unici (autore1 e autore2)
        assertEquals(2, risultati.size());
        assertTrue(risultati.contains(autore1));
        assertTrue(risultati.contains(autore2));
    }

    // --- TEST NULL CHECKS (AGGIUNGI / RIMUOVI) ---

    @Test
    @DisplayName("Aggiungi Messaggio: Null Input")
    void testAggiungiMessaggio_Null() {
        assertNull(messaggioService.aggiungiMessaggio(null));
        verify(messaggioDao, never()).aggiungiMessaggio(any());
    }

    @Test
    @DisplayName("Aggiungi Messaggio: Valid Input")
    void testAggiungiMessaggio_Valid() {
        Messaggio m = new Messaggio();
        when(messaggioDao.aggiungiMessaggio(m)).thenReturn(m);
        assertNotNull(messaggioService.aggiungiMessaggio(m));
        verify(messaggioDao).aggiungiMessaggio(m);
    }

    @Test
    @DisplayName("Rimuovi Messaggio: Null Input")
    void testRimuoviMessaggio_Null() {
        messaggioService.rimuoviMessaggio(null);
        verify(messaggioDao, never()).rimuoviMessaggio(any());
    }

    @Test
    @DisplayName("Rimuovi Messaggio: Valid Input")
    void testRimuoviMessaggio_Valid() {
        Messaggio m = new Messaggio();
        messaggioService.rimuoviMessaggio(m);
        verify(messaggioDao).rimuoviMessaggio(m);
    }

    // --- TEST DELEGA SEMPLICE ---

    @Test
    @DisplayName("Test Metodi di Delega Semplice")
    void testDelegations() {
        // Test rapidi per coprire i metodi pass-through
        messaggioService.trovaMessaggiInviati("1");
        verify(messaggioDao).trovaMessaggiInviati("1");

        messaggioService.trovaMessaggiRicevuti("1");
        verify(messaggioDao).trovaMessaggiRicevuti("1");

        messaggioService.trovaMessaggi("1", "2");
        verify(messaggioDao).trovaMessaggi("1", "2");

        messaggioService.trovaTutti();
        verify(messaggioDao).trovaTutti();

        messaggioService.trovaAvvisi();
        verify(messaggioDao).trovaAvvisi();

        messaggioService.trovaAvvisiAutore("a");
        verify(messaggioDao).trovaAvvisiAutore("a");

        LocalDateTime now = LocalDateTime.now();
        messaggioService.trovaMessaggiData(now);
        verify(messaggioDao).trovaMessaggiData(now);

        Topic t = new Topic();
        messaggioService.trovaTopic(t);
        verify(messaggioDao).trovaTopic(t);
    }

    @Test
    @DisplayName("Costruttore Vuoto")
    void testConstructor() {
        // Solo per coverage del costruttore vuoto se presente esplicitamente
        assertNotNull(new MessaggioService());
    }
}